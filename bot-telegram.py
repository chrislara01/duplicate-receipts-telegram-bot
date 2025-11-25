from dotenv import load_dotenv
import logging
import sqlite3
import os
import sys
import hashlib
import re
import unicodedata
import pytz
import gc
import asyncio
import time
from datetime import datetime
from io import BytesIO
from PIL import Image, ImageFilter, ImageEnhance, ImageOps
import imagehash
import easyocr
import numpy as np
from fuzzywuzzy import fuzz
from telegram import Update, ReplyKeyboardMarkup, ReplyKeyboardRemove, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    ConversationHandler,
    ContextTypes,
    MessageHandler,
    filters,
    CallbackQueryHandler,
)

# ------------------------- CONFIGURACIÓN -------------------------
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO,
    handlers=[logging.FileHandler('bot.log'), logging.StreamHandler()]
)

load_dotenv()

TOKEN = os.getenv('TOKEN')
DB_NAME = os.getenv('DB_NAME', 'comprobantes.db')
TIMEZONE = pytz.timezone(os.getenv('TIMEZONE', 'America/Havana'))

if not TOKEN:
    logging.error('Telegram bot token (TOKEN) not set in environment. Please add it to your .env file.')
    sys.exit(1)

# ------------------------- LISTA DE ENTIDADES (BANCOS Y EMISORES) -------------------------
BANCOS = {
    'BANAMEX': ['banamex', 'citibanamex'], 'BBVA': ['bbva', 'bancomer'],
    'BANCOPPEL': ['bancoppel', 'coppel'], 'BANORTE': ['banorte'],
    'HSBC': ['hsbc'], 'SANTANDER': ['santander'], 'SCOTIABANK': ['scotiabank'],
    'INBURSA': ['inbursa'], 'BANREGIO': ['banregio'], 'BANBAJIO': ['banbajío'],
    'AFIRME': ['afirme'], 'BANJERCITO': ['banjercito'], 'BANCO AZTECA': ['banco azteca'],
    'BANCO DEL BIENESTAR': ['banco del bienestar'], 'COMPARTAMOS': ['compartamos'],
    'INTERCAM BANCO': ['intercam banco'], 'MONEX': ['monex'], 'MULTIVA': ['multiva'],
    'OXXO': ['oxxo'], 'WALMART': ['walmart'], 'ELEKTRA': ['elektra']
}
BANCO_REGEX = re.compile(r'(?i)\b(' + '|'.join([alias for bancos in BANCOS.values() for alias in bancos]) + r')\b')

# ------------------------- EXPRESIONES REGULARES MEJORADAS -------------------------
MONTO_REGEX = re.compile(r'(?i)(?:monto|total|importe|valor|pago|transferido)?\s*[:$\-]*\s*\$?\s*([\d,]+\.?\d{0,2})')
FECHA_REGEX = re.compile(r'(?i)(\d{1,2})\s*(?:de)?\s*(ene|feb|mar|abr|may|jun|jul|ago|sep|oct|nov|dic)\s*(?:de)?\s*(\d{4})|(\d{1,2})[/-](\d{1,2})[/-](\d{4})')
FECHA_TRANSACCION_REGEX = re.compile(r'(?i)(\d{1,2}/(?:ene|feb|mar|abr|may|jun|jul|ago|sep|oct|nov|dic)/\d{4})\s+(\d{2}[:.]\d{2}(?::\d{2})?(?:\s*\(CST\))?)')
FOLIO_TRANSACCION_REGEX = re.compile(r'(?i)(?:folio|id|operación)\s*[:#]\s*([A-Z0-9]{6,10})')
CUENTA_ORIGEN_REGEX = re.compile(r'(?i)cuenta\s*origen\s*([A-ZÁÉÍÓÚÑ\s]+\s*\*+\d{4})')
BENEFICIARIO_REGEX = re.compile(r'(?i)(?:cuenta\s*destino|beneficiario|para|destino|a)\s*([A-ZÁÉÍÓÚÑ\s]+\s*\*+\d{4}(?:\s*[A-ZÁÉÍÓÚÑ\s]+\s*\*+\d{4})?)')
NUMEROS_REGEX = re.compile(r'\b\d+\.?\d*\b')
MESES = {'ene': '01', 'feb': '02', 'mar': '03', 'abr': '04', 'may': '05', 'jun': '06',
         'jul': '07', 'ago': '08', 'sep': '09', 'oct': '10', 'nov': '11', 'dic': '12'}

# ------------------------- BASE DE DATOS -------------------------
def init_db():
    with sqlite3.connect(DB_NAME) as conn:
        cursor = conn.cursor()
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS comprobantes (
                phash TEXT,
                content_hash TEXT,
                banco TEXT,
                monto REAL,
                referencia TEXT,
                fecha_comprobante TEXT,
                beneficiario TEXT,
                texto_completo TEXT,
                numeros_extraidos TEXT,
                folio_transaccion TEXT,
                fecha_transaccion TEXT,
                cuenta_origen TEXT,
                fecha_registro TEXT,
                chat_id INTEGER,
                message_id INTEGER,
                file_id TEXT,
                chat_title TEXT,
                UNIQUE(phash, content_hash)
            )
        ''')
        cursor.execute("PRAGMA table_info(comprobantes)")
        columns = [col[1] for col in cursor.fetchall()]
        if 'chat_title' not in columns:
            cursor.execute("ALTER TABLE comprobantes ADD COLUMN chat_title TEXT")
        conn.execute('CREATE INDEX IF NOT EXISTS idx_phash ON comprobantes(phash)')
        conn.execute('CREATE INDEX IF NOT EXISTS idx_content_hash ON comprobantes(content_hash)')
        conn.commit()

init_db()

# ------------------------- NORMALIZACIÓN Y LIMPIEZA -------------------------
def normalizar_texto(texto):
    if not texto:
        return ""
    texto = unicodedata.normalize('NFKD', texto).encode('ascii', 'ignore').decode('ascii')
    texto = re.sub(r'[^\w\s]', '', texto)  # Eliminar caracteres especiales
    texto = re.sub(r'\s+', ' ', texto).strip().upper()
    return texto

def limpiar_datos(datos, texto_completo):
    datos['banco'] = normalizar_texto(datos['banco'])
    datos['beneficiario'] = normalizar_texto(datos['beneficiario'])
    datos['referencia'] = normalizar_texto(datos['referencia'])
    datos['folio_transaccion'] = normalizar_texto(datos['folio_transaccion'])
    datos['fecha_transaccion'] = normalizar_texto(datos['fecha_transaccion'])
    datos['cuenta_origen'] = normalizar_texto(datos['cuenta_origen'])
    if datos['monto']:
        monto_str = str(datos['monto']).replace(',', '')
        datos['monto'] = float(monto_str)
    if datos['fecha_comprobante']:
        parts = datos['fecha_comprobante'].split()
        if len(parts) > 1:
            datos['fecha_comprobante'] = f"{parts[0]} {parts[1]}"
        else:
            datos['fecha_comprobante'] = f"{parts[0]} 00:00"
    datos['texto_completo'] = normalizar_texto(texto_completo)
    datos['numeros_extraidos'] = ' '.join(sorted(NUMEROS_REGEX.findall(texto_completo)))
    return datos

# ------------------------- PROCESAMIENTO DE IMÁGENES -------------------------
def mejorar_imagen(img):
    try:
        img = ImageOps.exif_transpose(img).convert('L')
        img.thumbnail((1024, 1024))
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(3.0)
        img = img.filter(ImageFilter.SHARPEN)
        img = img.point(lambda x: 0 if x < 140 else 255)
        return img
    except Exception as e:
        logging.error(f"Error procesando imagen: {str(e)}")
        return img

def calcular_hashes(file_data):
    try:
        img = Image.open(BytesIO(file_data))
        img_proc = mejorar_imagen(img).resize((256, 256), Image.LANCZOS)
        phash = str(imagehash.phash(img_proc))
        content_hash = hashlib.sha256(file_data).hexdigest()
        return {'phash': phash, 'content_hash': content_hash}
    except Exception as e:
        logging.error(f"Error calculando hashes: {str(e)}")
        return {'phash': '', 'content_hash': ''}

OCR_READER = easyocr.Reader(['es'], gpu=False, quantize=True)

def extraer_texto(file_data):
    try:
        img = Image.open(BytesIO(file_data))
        img_mejorada = mejorar_imagen(img)
        img_array = np.array(img_mejorada)
        texto = ' '.join([res[1] for res in OCR_READER.readtext(img_array, paragraph=True)])
        return texto
    except Exception as e:
        logging.error(f"Error en OCR: {str(e)}")
        return ""
    finally:
        gc.collect()

def parsear_datos(texto):
    datos = {
        'monto': None, 'fecha_comprobante': None, 'referencia': None,
        'banco': 'DESCONOCIDO', 'beneficiario': None, 'moneda': 'MXN', 'errors': [],
        'numeros_extraidos': None, 'folio_transaccion': None, 'fecha_transaccion': None,
        'cuenta_origen': None
    }

    # Banco/Entidad
    banco_match = BANCO_REGEX.search(texto)
    if banco_match:
        for banco, aliases in BANCOS.items():
            if any(alias.lower() in banco_match.group(0).lower() for alias in aliases):
                datos['banco'] = banco
                break

    # Monto
    monto_matches = MONTO_REGEX.findall(texto)
    if monto_matches:
        try:
            monto_str = monto_matches[0].replace(',', '')  # Tomar el primer monto encontrado
            datos['monto'] = float(monto_str)
        except ValueError:
            datos['errors'].append("Monto no detectado o inválido")
    else:
        datos['errors'].append("Monto no detectado")

    # Fecha comprobante (general)
    fecha_match = FECHA_REGEX.search(texto)
    if fecha_match:
        if fecha_match.group(1):  # Formato con nombre de mes
            dia, mes, anio = fecha_match.group(1), fecha_match.group(2), fecha_match.group(3)
            mes_num = MESES.get(mes.lower(), '01')
            datos['fecha_comprobante'] = f"{dia.zfill(2)}/{mes_num}/{anio[-2:]}"
        else:  # Formato numérico
            dia, mes, anio = fecha_match.group(4), fecha_match.group(5), fecha_match.group(6)
            datos['fecha_comprobante'] = f"{dia.zfill(2)}/{mes.zfill(2)}/{anio[-2:]}"
    else:
        datos['errors'].append("Fecha no detectada")

    # Fecha y hora de transacción
    fecha_transaccion_match = FECHA_TRANSACCION_REGEX.search(texto)
    if fecha_transaccion_match:
        fecha, hora = fecha_transaccion_match.group(1), fecha_transaccion_match.group(2)
        datos['fecha_transaccion'] = f"{fecha} {hora.replace('.', ':')}"  # Normalizar . a :

    # Folio de transacción
    folio_match = FOLIO_TRANSACCION_REGEX.search(texto)
    if folio_match:
        datos['folio_transaccion'] = folio_match.group(1)
    else:
        # Intentar encontrar un folio al final del texto (como en este caso)
        folio_alt_match = re.search(r'folio\s*[:]\s*(\d{6,10})\b', texto.lower())
        if folio_alt_match:
            datos['folio_transaccion'] = folio_alt_match.group(1)

    # Cuenta origen
    cuenta_origen_match = CUENTA_ORIGEN_REGEX.search(texto)
    if cuenta_origen_match:
        datos['cuenta_origen'] = cuenta_origen_match.group(1)

    # Beneficiario/Cuenta destino
    ben_match = BENEFICIARIO_REGEX.search(texto)
    if ben_match:
        datos['beneficiario'] = ben_match.group(1)

    return datos

# ------------------------- DETECCIÓN DE DUPLICADOS -------------------------
def comparar_datos(datos1, datos2):
    score = 0
    total_campos_disponibles = 0

    # Criterio 1: Folio de transacción
    if datos1['folio_transaccion'] and datos2['folio_transaccion']:
        total_campos_disponibles += 1
        if datos1['folio_transaccion'] == datos2['folio_transaccion']:
            score += 3  # Alto peso, es un identificador único

    # Criterio 2: Fecha y hora de transacción
    if datos1['fecha_transaccion'] and datos2['fecha_transaccion']:
        total_campos_disponibles += 1
        if fuzz.ratio(datos1['fecha_transaccion'], datos2['fecha_transaccion']) > 95:  # Tolerancia para pequeñas diferencias
            score += 2

    # Criterio 3: Monto
    if datos1['monto'] and datos2['monto']:
        total_campos_disponibles += 1
        if abs(datos1['monto'] - datos2['monto']) <= 1:
            score += 2

    # Criterio 4: Beneficiario/Cuenta destino
    if datos1['beneficiario'] and datos2['beneficiario']:
        total_campos_disponibles += 1
        if fuzz.ratio(datos1['beneficiario'], datos2['beneficiario']) > 85:
            score += 1

    # Criterio 5: Cuenta origen
    if datos1['cuenta_origen'] and datos2['cuenta_origen']:
        total_campos_disponibles += 1
        if fuzz.ratio(datos1['cuenta_origen'], datos2['cuenta_origen']) > 85:
            score += 1

    # Criterios adicionales para apoyo
    if datos1['banco'] == datos2['banco'] and datos1['banco'] != 'DESCONOCIDO':
        score += 1

    if datos1['texto_completo'] and datos2['texto_completo']:
        if fuzz.ratio(datos1['texto_completo'], datos2['texto_completo']) > 90:
            score += 1

    if datos1['numeros_extraidos'] and datos2['numeros_extraidos']:
        nums1 = set(datos1['numeros_extraidos'].split())
        nums2 = set(datos2['numeros_extraidos'].split())
        intersection = nums1 & nums2
        union = nums1 | nums2
        similarity = len(intersection) / len(union) if union else 0
        if similarity > 0.8:
            score += 1

    # Umbral dinámico
    umbral = max(4, total_campos_disponibles * 1.2)  # Reducido el umbral para ser más flexible
    return score, umbral

def verificar_duplicado(file_id, file_data, datos, texto):
    try:
        hashes = calcular_hashes(file_data)
        with sqlite3.connect(DB_NAME) as conn:
            cursor = conn.cursor()
            cursor.execute('SELECT * FROM comprobantes WHERE phash = ? AND content_hash = ?',
                          (hashes['phash'], hashes['content_hash']))
            result = cursor.fetchone()
            if result:
                return True, dict(zip([c[0] for c in cursor.description], result))

            # Comparación aproximada
            cursor.execute('SELECT * FROM comprobantes')
            for row in cursor.fetchall():
                original = dict(zip([c[0] for c in cursor.description], row))
                score, umbral = comparar_datos(datos, original)
                if score >= umbral:
                    return True, original
        return False, None
    except Exception as e:
        logging.error(f"Error verificando duplicado: {str(e)}")
        return False, None

# ------------------------- ORQUESTADOR DE FLUJO -------------------------
async def orquestador(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        message = update.effective_message
        file = message.photo[-1] if message.photo else (message.document if message.document else None)
        if not file:
            logging.error("No se detectó un archivo válido")
            return

        file_id = file.file_id
        file_obj = await file.get_file()
        file_data = await file_obj.download_as_bytearray()

        # Ingesta y OCR
        texto = extraer_texto(file_data)
        datos = parsear_datos(texto)
        datos = limpiar_datos(datos, texto)

        # Verificar duplicado
        es_duplicado, original = verificar_duplicado(file_id, file_data, datos, texto)
        if es_duplicado:
            fecha_original = datetime.fromisoformat(original['fecha_registro']).astimezone(TIMEZONE)
            grupo_info = original.get('chat_title', "Desconocido")
            chat_id_original = original['chat_id']
            message_id_original = original['message_id']
            link_original = f"https://t.me/c/{str(chat_id_original).replace('-100', '')}/{message_id_original}"

            # <-- CAMBIO IMPORTANTE: quitar parse_mode y Markdown -->
            respuesta = (
                f"⚠️ COMPROBANTE DUPLICADO ⚠️\n"
                f"🕒 Fecha original: {fecha_original.strftime('%d/%m/%Y %H:%M:%S')}\n"
                f"📢 Grupo/Canal: {grupo_info}\n"
                f"🔗 Ver original: {link_original}"
            )
            await message.reply_text(respuesta)
            logging.info("Duplicado detectado y mensaje enviado al usuario.")
            return
        
        # Guardar en base de datos
        hashes = calcular_hashes(file_data)
        chat_title = message.chat.title or message.chat.username or "Desconocido"
        with sqlite3.connect(DB_NAME) as conn:
            conn.execute('''
                INSERT OR IGNORE INTO comprobantes
                (phash, content_hash, banco, monto, referencia, fecha_comprobante, beneficiario, texto_completo, numeros_extraidos, folio_transaccion, fecha_transaccion, cuenta_origen, fecha_registro, chat_id, message_id, file_id, chat_title)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                hashes['phash'], hashes['content_hash'], datos['banco'], datos['monto'],
                datos['referencia'], datos['fecha_comprobante'], datos['beneficiario'], datos['texto_completo'],
                datos['numeros_extraidos'], datos['folio_transaccion'], datos['fecha_transaccion'],
                datos['cuenta_origen'], datetime.now(TIMEZONE).isoformat(), message.chat.id, message.message_id, file_id, chat_title
            ))
            conn.commit()

        logging.info(f"Nuevo comprobante procesado: {datos}")

    except Exception as e:
        logging.error(f"Error en orquestador: {str(e)}", exc_info=True)

# ------------------------- CONVERSACIÓN PARA LISTAR AUTOS -------------------------
CAR_TYPE, CAR_COLOR, CAR_MILEAGE_DECISION, CAR_MILEAGE, PHOTO, SUMMARY = range(6)

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    reply_keyboard = [['Sedan', 'SUV', 'Sports', 'Electric']]
    await update.message.reply_text(
        '<b>Welcome to the Car Sales Listing Bot!\nWhat is your car type?</b>',
        parse_mode='HTML',
        reply_markup=ReplyKeyboardMarkup(reply_keyboard, one_time_keyboard=True, resize_keyboard=True),
    )
    return CAR_TYPE

async def car_type(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data['car_type'] = update.message.text
    keyboard = [
        [InlineKeyboardButton('Red', callback_data='Red')],
        [InlineKeyboardButton('Blue', callback_data='Blue')],
        [InlineKeyboardButton('Black', callback_data='Black')],
        [InlineKeyboardButton('White', callback_data='White')],
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    await update.message.reply_text(
        f'<b>You selected {update.message.text}.\nWhat color is your car?</b>',
        parse_mode='HTML',
        reply_markup=reply_markup
    )
    return CAR_COLOR

async def car_color(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data['car_color'] = query.data
    keyboard = [
        [InlineKeyboardButton('Fill', callback_data='Fill')],
        [InlineKeyboardButton('Skip', callback_data='Skip')],
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    await query.edit_message_text(
        text=f'<b>You selected {query.data} color.\nWould you like to enter the mileage?</b>',
        parse_mode='HTML',
        reply_markup=reply_markup
    )
    return CAR_MILEAGE_DECISION

async def car_mileage_decision(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if query.data == 'Fill':
        await query.edit_message_text('<b>Please type in the mileage (e.g., 50000):</b>', parse_mode='HTML')
        return CAR_MILEAGE
    context.user_data['car_mileage'] = 'Not provided'
    await query.edit_message_text('<b>Please upload a photo of your car, or send /skip.</b>', parse_mode='HTML')
    return PHOTO

async def car_mileage(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data['car_mileage'] = update.message.text
    await update.message.reply_text(
        '<b>Mileage noted.\nPlease upload a photo of your car, or send /skip.</b>',
        parse_mode='HTML'
    )
    return PHOTO

async def photo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    try:
        file_obj = await update.message.photo[-1].get_file()
        context.user_data['car_photo'] = file_obj.file_id
    except Exception as e:
        logging.error(f"Error obtaining photo: {str(e)}")
        context.user_data['car_photo'] = 'Not provided'
    return await summary(update, context)

async def skip_photo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data['car_photo'] = 'Not provided'
    return await summary(update, context)

async def summary(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    selections = context.user_data
    summary_text = (
        f"<b>Here's your car listing:\n</b>"
        f"<b>Car Type:</b> {selections.get('car_type', 'N/A')}\n"
        f"<b>Color:</b> {selections.get('car_color', 'N/A')}\n"
        f"<b>Mileage:</b> {selections.get('car_mileage', 'N/A')}\n"
        f"<b>Photo:</b> {'Uploaded' if selections.get('car_photo', 'Not provided') != 'Not provided' else 'Not provided'}"
    )
    chat_id = update.effective_chat.id
    if selections.get('car_photo', 'Not provided') != 'Not provided':
        await context.bot.send_photo(chat_id=chat_id, photo=selections['car_photo'], caption=summary_text, parse_mode='HTML')
    else:
        await context.bot.send_message(chat_id=chat_id, text=summary_text, parse_mode='HTML')
    return ConversationHandler.END

async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.message.reply_text('Bye! Hope to talk to you again soon.', reply_markup=ReplyKeyboardRemove())
    return ConversationHandler.END

# ------------------------- MAIN -------------------------
def main() -> None:
    application = Application.builder().token(TOKEN).build()

    application.add_handler(MessageHandler(filters.PHOTO | filters.Document.IMAGE, orquestador))

    conv_handler = ConversationHandler(
        entry_points=[CommandHandler('start', start)],
        states={
            CAR_TYPE: [MessageHandler(filters.TEXT & ~filters.COMMAND, car_type)],
            CAR_COLOR: [CallbackQueryHandler(car_color)],
            CAR_MILEAGE_DECISION: [CallbackQueryHandler(car_mileage_decision)],
            CAR_MILEAGE: [MessageHandler(filters.TEXT & ~filters.COMMAND, car_mileage)],
            PHOTO: [MessageHandler(filters.PHOTO, photo), CommandHandler('skip', skip_photo)],
            SUMMARY: [MessageHandler(filters.ALL, summary)]
        },
        fallbacks=[CommandHandler('cancel', cancel)],
        per_message=False
    )
    application.add_handler(conv_handler)

    application.run_polling(drop_pending_updates=True)

if __name__ == '__main__':
    while True:
        try:
            main()
        except Exception as ex:
            logging.error("Bot crashed: %s", ex, exc_info=True)
            gc.collect()
            time.sleep(5)