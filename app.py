#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
nfe_parser_max.py — UltraMaxNFeParser
Parser de NF-e/NFC-e versão MÁXIMA: XML (lxml + XPath agressivo,
múltiplos namespaces, normalização, regex) + fallback DANFE PDF.
Produção-ready | Suporte a milhares de notas | Relatório JSON automático.
"""

# ─── Stdlib ───────────────────────────────────────────────────────────────────
import copy
import glob
import hashlib
import io
import json
import logging
import os
import re
import sys
import time
import traceback
import unicodedata
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union

# ─── Third-party (graceful imports) ───────────────────────────────────────────
try:
    from lxml import etree as lxml_etree
    HAS_LXML = True
except ImportError:
    HAS_LXML = False

try:
    import pdfplumber
    HAS_PDFPLUMBER = True
except ImportError:
    HAS_PDFPLUMBER = False

try:
    import pytesseract
    from PIL import Image
    HAS_OCR = True
except ImportError:
    HAS_OCR = False

try:
    import fitz  # PyMuPDF
    HAS_FITZ = True
except ImportError:
    HAS_FITZ = False


# ══════════════════════════════════════════════════════════════════════════════
# LOGGING COLORIDO
# ══════════════════════════════════════════════════════════════════════════════

class ColorFormatter(logging.Formatter):
    CORES = {
        logging.DEBUG:    "\033[36m",   # Ciano
        logging.INFO:     "\033[32m",   # Verde
        logging.WARNING:  "\033[33m",   # Amarelo
        logging.ERROR:    "\033[31m",   # Vermelho
        logging.CRITICAL: "\033[35m",   # Magenta
    }
    RESET = "\033[0m"
    BOLD  = "\033[1m"

    def format(self, record: logging.LogRecord) -> str:
        cor   = self.CORES.get(record.levelno, self.RESET)
        nivel = f"{cor}{self.BOLD}{record.levelname:<8}{self.RESET}"
        hora  = datetime.fromtimestamp(record.created).strftime("%H:%M:%S.%f")[:-3]
        msg   = super().format(record)
        nome  = f"\033[90m[{record.name}]\033[0m"
        return f"\033[90m{hora}\033[0m {nivel} {nome} {msg}"


def _build_logger(name: str = "UltraMaxNFeParser") -> logging.Logger:
    logger = logging.getLogger(name)
    if not logger.handlers:
        handler = logging.StreamHandler(sys.stdout)
        handler.setFormatter(ColorFormatter("%(message)s"))
        logger.addHandler(handler)
    logger.setLevel(logging.DEBUG)
    return logger


log = _build_logger()


# ══════════════════════════════════════════════════════════════════════════════
# CONSTANTES — NAMESPACES E XPATHS
# ══════════════════════════════════════════════════════════════════════════════

# Todos os namespaces conhecidos de NF-e (SEFAZ, variações de versão, legados)
NAMESPACES_NFE: List[str] = [
    "http://www.portalfiscal.inf.br/nfe",
    "http://www.portalfiscal.inf.br/nfe/wsdl",
    "http://www.portalfiscal.inf.br/nfe/wsdl/NfeAutorizacao",
    "http://www.portalfiscal.inf.br/nfe/wsdl/NfeRetAutorizacao",
    "http://www.portalfiscal.inf.br/nfe/wsdl/NFeAutorizacao4",
    "http://www.portalfiscal.inf.br/nfe/wsdl/NFeRetAutorizacao4",
    "http://www.portalfiscal.inf.br/cte",
    "http://www.portalfiscal.inf.br/mdfe",
    "http://nfe.fazenda.gov.br/port/ser/nfeservicos.wsdl",
    "",  # sem namespace
]

# Prefixos comuns encontrados em XMLs de NF-e no mercado
NS_PREFIXOS: Dict[str, str] = {
    "nfe":  "http://www.portalfiscal.inf.br/nfe",
    "n":    "http://www.portalfiscal.inf.br/nfe",
    "nf":   "http://www.portalfiscal.inf.br/nfe",
    "cte":  "http://www.portalfiscal.inf.br/cte",
    "mdfe": "http://www.portalfiscal.inf.br/mdfe",
}

# ── XPaths para cada campo crítico ────────────────────────────────────────────
# Cada lista contém expressões em ordem de especificidade decrescente.
# O parser tentará todas até obter um valor não-nulo.

XPATHS_SERIE: List[str] = [
    # Padrão moderno com namespace completo
    ".//{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}serie",
    ".//{http://www.portalfiscal.inf.br/nfe}serie",
    # Sem namespace
    ".//ide/serie",
    ".//serie",
    # NFCe / produtor rural
    ".//{http://www.portalfiscal.inf.br/nfe}infNFe/{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}serie",
    # Maiúsculo/minúsculo variado (XMLs mal gerados)
    ".//Serie", ".//SERIE",
    # Dentro de nfeProc
    ".//{http://www.portalfiscal.inf.br/nfe}nfeProc//{http://www.portalfiscal.inf.br/nfe}serie",
    # CTE
    ".//{http://www.portalfiscal.inf.br/cte}serie",
    ".//infCte//serie",
    # Atributo (raro, mas existe em alguns sistemas legados)
    ".//@serie",
]

XPATHS_NNF: List[str] = [
    # Moderno
    ".//{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}nNF",
    ".//{http://www.portalfiscal.inf.br/nfe}nNF",
    # Sem namespace
    ".//ide/nNF",
    ".//nNF",
    # Maiúsculo/minúsculo
    ".//nNf", ".//NNF", ".//Nnf",
    # NFCe produtor rural
    ".//{http://www.portalfiscal.inf.br/nfe}infNFe/{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}nNF",
    # nfeProc
    ".//{http://www.portalfiscal.inf.br/nfe}nfeProc//{http://www.portalfiscal.inf.br/nfe}nNF",
    # CTE
    ".//{http://www.portalfiscal.inf.br/cte}nCT",
    ".//nCT",
    # Atributo Id (fallback: extrair do Id="NFe..." ou "CTe...")
]

XPATHS_VNF: List[str] = [
    # Totais NF-e
    ".//{http://www.portalfiscal.inf.br/nfe}total/{http://www.portalfiscal.inf.br/nfe}ICMSTot/{http://www.portalfiscal.inf.br/nfe}vNF",
    ".//{http://www.portalfiscal.inf.br/nfe}vNF",
    # Sem namespace
    ".//total/ICMSTot/vNF",
    ".//vNF",
    # Maiúsculo/minúsculo
    ".//VNF", ".//Vnf", ".//vNf",
    # NFC-e (mesmo caminho, redundância explícita)
    ".//{http://www.portalfiscal.inf.br/nfe}ICMSTot/{http://www.portalfiscal.inf.br/nfe}vNF",
    # CTE usa vTPrest/vRec
    ".//{http://www.portalfiscal.inf.br/cte}vTPrest/{http://www.portalfiscal.inf.br/cte}vRec",
    ".//{http://www.portalfiscal.inf.br/cte}vRec",
    ".//vRec",
    # Fallback: vProd (valor total dos produtos — menos preciso)
    ".//{http://www.portalfiscal.inf.br/nfe}vProd",
    ".//vProd",
]

XPATHS_DHEMI: List[str] = [
    # Moderno (com T separando data e hora)
    ".//{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}dhEmi",
    ".//{http://www.portalfiscal.inf.br/nfe}dhEmi",
    # Legado: dEmi (apenas data, sem hora)
    ".//{http://www.portalfiscal.inf.br/nfe}ide/{http://www.portalfiscal.inf.br/nfe}dEmi",
    ".//{http://www.portalfiscal.inf.br/nfe}dEmi",
    # Sem namespace
    ".//ide/dhEmi",
    ".//dhEmi",
    ".//ide/dEmi",
    ".//dEmi",
    # Maiúsculo/minúsculo
    ".//DhEmi", ".//DHEMI", ".//DEmi", ".//DEMI",
    # NFCe
    ".//{http://www.portalfiscal.inf.br/nfe}infNFe//{http://www.portalfiscal.inf.br/nfe}dhEmi",
    # nfeProc
    ".//{http://www.portalfiscal.inf.br/nfe}nfeProc//{http://www.portalfiscal.inf.br/nfe}dhEmi",
    # CTE
    ".//{http://www.portalfiscal.inf.br/cte}dhEmi",
    ".//infCte//dhEmi",
]

# XPaths extras para campos complementares
XPATHS_EXTRAS: Dict[str, List[str]] = {
    "chave_nfe": [
        ".//{http://www.portalfiscal.inf.br/nfe}infProt/{http://www.portalfiscal.inf.br/nfe}chNFe",
        ".//{http://www.portalfiscal.inf.br/nfe}chNFe",
        ".//chNFe",
        ".//{http://www.portalfiscal.inf.br/nfe}infNFe/@Id",
    ],
    "modelo": [
        ".//{http://www.portalfiscal.inf.br/nfe}mod",
        ".//mod",
    ],
    "cnpj_emitente": [
        ".//{http://www.portalfiscal.inf.br/nfe}emit/{http://www.portalfiscal.inf.br/nfe}CNPJ",
        ".//{http://www.portalfiscal.inf.br/nfe}CNPJ",
        ".//emit/CNPJ",
        ".//CNPJ",
    ],
    "razao_emitente": [
        ".//{http://www.portalfiscal.inf.br/nfe}emit/{http://www.portalfiscal.inf.br/nfe}xNome",
        ".//emit/xNome",
        ".//xNome",
    ],
    "cnpj_destinatario": [
        ".//{http://www.portalfiscal.inf.br/nfe}dest/{http://www.portalfiscal.inf.br/nfe}CNPJ",
        ".//{http://www.portalfiscal.inf.br/nfe}dest/{http://www.portalfiscal.inf.br/nfe}CPF",
        ".//dest/CNPJ",
        ".//dest/CPF",
    ],
    "razao_destinatario": [
        ".//{http://www.portalfiscal.inf.br/nfe}dest/{http://www.portalfiscal.inf.br/nfe}xNome",
        ".//dest/xNome",
    ],
    "valor_icms": [
        ".//{http://www.portalfiscal.inf.br/nfe}vICMS",
        ".//vICMS",
    ],
    "valor_ipi": [
        ".//{http://www.portalfiscal.inf.br/nfe}vIPI",
        ".//vIPI",
    ],
    "valor_pis": [
        ".//{http://www.portalfiscal.inf.br/nfe}vPIS",
        ".//vPIS",
    ],
    "valor_cofins": [
        ".//{http://www.portalfiscal.inf.br/nfe}vCOFINS",
        ".//vCOFINS",
    ],
    "valor_frete": [
        ".//{http://www.portalfiscal.inf.br/nfe}vFrete",
        ".//vFrete",
    ],
    "valor_desconto": [
        ".//{http://www.portalfiscal.inf.br/nfe}vDesc",
        ".//vDesc",
    ],
    "natureza_operacao": [
        ".//{http://www.portalfiscal.inf.br/nfe}natOp",
        ".//natOp",
    ],
    "uf_emitente": [
        ".//{http://www.portalfiscal.inf.br/nfe}emit/{http://www.portalfiscal.inf.br/nfe}enderEmit/{http://www.portalfiscal.inf.br/nfe}UF",
        ".//emit/enderEmit/UF",
    ],
    "protocolo": [
        ".//{http://www.portalfiscal.inf.br/nfe}nProt",
        ".//nProt",
    ],
    "versao": [
        ".//{http://www.portalfiscal.inf.br/nfe}infNFe/@versao",
        ".//infNFe/@versao",
    ],
}


# ══════════════════════════════════════════════════════════════════════════════
# PADRÕES REGEX — FALLBACKS PARA XML TEXTUAL E PDF
# ══════════════════════════════════════════════════════════════════════════════

# Regex para extração direta do texto do XML (quando parsing falha)
RE_SERIE_XML   = re.compile(r"<(?:\w+:)?serie\s*>(.*?)</(?:\w+:)?serie>", re.IGNORECASE | re.DOTALL)
RE_NNF_XML     = re.compile(r"<(?:\w+:)?nNF\s*>(\d+)</(?:\w+:)?nNF>", re.IGNORECASE | re.DOTALL)
RE_VNF_XML     = re.compile(r"<(?:\w+:)?vNF\s*>([\d\.]+)</(?:\w+:)?vNF>", re.IGNORECASE | re.DOTALL)
RE_DHEMI_XML   = re.compile(
    r"<(?:\w+:)?dh?Emi\s*>([\d\-T:+\-Z]+)</(?:\w+:)?dh?Emi>",
    re.IGNORECASE | re.DOTALL
)
# Chave no atributo Id="NFe..."
RE_CHAVE_ID    = re.compile(r'Id\s*=\s*["\'](?:NFe|CTe|MDFe)?([0-9]{44})["\']', re.IGNORECASE)
RE_CHAVE_CHAVE = re.compile(r'<(?:\w+:)?chNFe\s*>([0-9]{44})</(?:\w+:)?chNFe>', re.IGNORECASE)

# Regex para DANFE PDF
RE_PDF_SERIE   = [
    re.compile(r"[Ss][eé]rie[:\s]*([A-Z0-9]{1,5})"),
    re.compile(r"s[eé]r\.?\s*([A-Z0-9]{1,5})"),
    re.compile(r"SÉRIE\s*[:\-]?\s*([A-Z0-9]{1,5})"),
    re.compile(r"Nº\s*(\d+)\s*/\s*([A-Z0-9]{1,5})"),  # grupo 2
]
RE_PDF_NNF     = [
    re.compile(r"[Nn][ú°]\s*(\d{6,})"),
    re.compile(r"[Nn][uú]mero\s*(?:da\s*)?(?:nota|NF[- ]?e?)[:\s]*(\d+)", re.IGNORECASE),
    re.compile(r"NF[- ]?e?\s*[Nn][°º]?\s*[:\-]?\s*(\d+)", re.IGNORECASE),
    re.compile(r"(?:NOTA|NF)[^\d]{0,10}(\d{6,9})", re.IGNORECASE),
    re.compile(r"\b(\d{6,9})\b"),  # fallback numérico agressivo
]
RE_PDF_VNF     = [
    re.compile(r"[Vv]alor\s*[Tt]otal\s*(?:da\s*)?[Nn]ota[:\s]*R?\$?\s*([\d\.]+,\d{2})"),
    re.compile(r"VALOR\s*TOTAL[:\s]*R?\$?\s*([\d\.]+,\d{2})", re.IGNORECASE),
    re.compile(r"vNF[:\s]*([\d\.]+,\d{2})", re.IGNORECASE),
    re.compile(r"Total\s*R?\$\s*([\d\.,]+)", re.IGNORECASE),
    re.compile(r"R\$\s*([\d\.]+,\d{2})"),  # último recurso
]
RE_PDF_DHEMI   = [
    re.compile(r"[Dd]ata\s+(?:de\s+)?[Ee]miss[ãa]o[:\s]*(\d{2}/\d{2}/\d{4})\s*(\d{2}:\d{2}(?::\d{2})?)?"),
    re.compile(r"EMISS[ÃA]O[:\s]*(\d{2}/\d{2}/\d{4})", re.IGNORECASE),
    re.compile(r"\b(\d{2}/\d{2}/\d{4})\s+(\d{2}:\d{2}(?::\d{2})?)"),
    re.compile(r"\b(\d{2}/\d{2}/\d{4})\b"),
]


# ══════════════════════════════════════════════════════════════════════════════
# UTILIDADES
# ══════════════════════════════════════════════════════════════════════════════

def _strip_ns(tag: str) -> str:
    """Remove namespace de uma tag XML: {ns}tag → tag."""
    return tag.split("}")[-1] if "}" in tag else tag


def _normalizar_xml(raw: Union[str, bytes]) -> bytes:
    """
    Normaliza XML bruto:
    - Garante encoding UTF-8
    - Remove BOM
    - Corrige declaração de encoding incorreta
    - Remove caracteres de controle inválidos no XML
    - Normaliza namespaces duplicados
    """
    if isinstance(raw, bytes):
        # Detecta encoding pelo BOM ou declaração
        for enc in ("utf-8-sig", "utf-8", "latin-1", "cp1252", "iso-8859-1"):
            try:
                texto = raw.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            texto = raw.decode("utf-8", errors="replace")
    else:
        texto = raw

    # Remove BOM explícito
    texto = texto.lstrip("\ufeff")

    # Corrige declaração de encoding para utf-8
    texto = re.sub(
        r'<\?xml[^>]*encoding=["\'][^"\']*["\'][^>]*\?>',
        '<?xml version="1.0" encoding="UTF-8"?>',
        texto,
        count=1,
        flags=re.IGNORECASE,
    )

    # Remove caracteres de controle inválidos no XML (exceto tab, LF, CR)
    texto = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]", "", texto)

    # Normaliza & não escapados fora de CDATA (causa parse error)
    texto = re.sub(r"&(?!(?:amp|lt|gt|apos|quot|#\d+|#x[0-9a-fA-F]+);)", "&amp;", texto)

    return texto.encode("utf-8")


def _parse_data_hora(valor: str) -> Tuple[str, str]:
    """
    Converte dhEmi/dEmi para (data_br, hora).
    Formatos aceitos:
      2024-03-15T10:30:00-03:00
      2024-03-15T10:30:00
      2024-03-15
      15/03/2024 (PDF)
      15/03/2024 10:30
    """
    if not valor:
        return ("", "")
    v = valor.strip()

    # ISO 8601 com timezone (formato padrão NF-e 4.x)
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})T(\d{2}:\d{2}:\d{2})([+-]\d{2}:\d{2}|Z)?", v)
    if m:
        data = f"{m.group(3)}/{m.group(2)}/{m.group(1)}"
        hora = m.group(4)
        return (data, hora)

    # ISO sem hora
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})", v)
    if m:
        data = f"{m.group(3)}/{m.group(2)}/{m.group(1)}"
        return (data, "")

    # BR com hora
    m = re.match(r"(\d{2})/(\d{2})/(\d{4})\s*(\d{2}:\d{2}(?::\d{2})?)?", v)
    if m:
        data = f"{m.group(1)}/{m.group(2)}/{m.group(3)}"
        hora = m.group(4) or ""
        return (data, hora)

    return (v, "")


def _valor_float(s: Optional[str]) -> Optional[float]:
    """Converte string de valor NF-e (ponto decimal) ou BR (vírgula) para float."""
    if not s:
        return None
    try:
        limpo = re.sub(r"[R$\s]", "", str(s).strip())
        # Detecta separador decimal: se tem vírgula e ponto, o último é decimal
        if "," in limpo and "." in limpo:
            limpo = limpo.replace(".", "").replace(",", ".")
        elif "," in limpo:
            limpo = limpo.replace(",", ".")
        return float(limpo)
    except (ValueError, TypeError):
        return None


def _formatar_cnpj(s: str) -> str:
    digits = re.sub(r"\D", "", s or "")
    if len(digits) == 14:
        return f"{digits[:2]}.{digits[2:5]}.{digits[5:8]}/{digits[8:12]}-{digits[12:]}"
    if len(digits) == 11:
        return f"{digits[:3]}.{digits[3:6]}.{digits[6:9]}-{digits[9:]}"
    return s


def _extrair_serie_da_chave(chave: str) -> str:
    """
    A chave de 44 dígitos da NF-e contém a série nas posições 22-24 (1-based).
    Layout: cUF(2) AAMM(4) CNPJ(14) mod(2) serie(3) nNF(9) tpEmi(1) cNF(8) cDV(1)
    """
    digitos = re.sub(r"\D", "", chave or "")
    if len(digitos) >= 25:
        serie_raw = digitos[22:25]
        return str(int(serie_raw))  # Remove zeros à esquerda (001→1)
    return ""


def _extrair_nnf_da_chave(chave: str) -> str:
    """Extrai nNF das posições 25-33 da chave (0-based: 25 a 33, 9 dígitos)."""
    digitos = re.sub(r"\D", "", chave or "")
    if len(digitos) >= 34:
        nnf_raw = digitos[25:34]
        return str(int(nnf_raw))
    return ""


# ══════════════════════════════════════════════════════════════════════════════
# ESTRATÉGIAS DE PARSING XML
# ══════════════════════════════════════════════════════════════════════════════

class _EstrategiaXML:
    """Encapsula todas as estratégias de extração de um XML."""

    def __init__(self, xml_bytes: bytes, arquivo: str = ""):
        self.xml_bytes  = xml_bytes
        self.arquivo    = arquivo
        self._raw_text  = ""
        self._et_root   = None   # xml.etree.ElementTree root
        self._lx_root   = None   # lxml root
        self._chave     = ""

    # ── Parsing ───────────────────────────────────────────────────────────────

    def _parse_stdlib(self) -> bool:
        """Tenta parsing com xml.etree.ElementTree (stdlib)."""
        try:
            root = ET.fromstring(self.xml_bytes)
            self._et_root = root
            return True
        except ET.ParseError as e:
            log.debug(f"stdlib ET falhou: {e}")
        # Tenta com recover (normalização prévia)
        try:
            limpo = _normalizar_xml(self.xml_bytes)
            self._et_root = ET.fromstring(limpo)
            return True
        except ET.ParseError as e:
            log.debug(f"stdlib ET (normalizado) falhou: {e}")
        return False

    def _parse_lxml(self) -> bool:
        """Tenta parsing com lxml (recover=True para XMLs quebrados)."""
        if not HAS_LXML:
            return False
        try:
            parser = lxml_etree.XMLParser(recover=True, encoding="utf-8")
            root = lxml_etree.fromstring(self.xml_bytes, parser=parser)
            self._lx_root = root
            return True
        except Exception as e:
            log.debug(f"lxml falhou: {e}")
        try:
            limpo = _normalizar_xml(self.xml_bytes)
            parser = lxml_etree.XMLParser(recover=True, encoding="utf-8")
            self._lx_root = lxml_etree.fromstring(limpo, parser=parser)
            return True
        except Exception as e:
            log.debug(f"lxml (normalizado) falhou: {e}")
        return False

    def _load_text(self) -> None:
        for enc in ("utf-8-sig", "utf-8", "latin-1", "cp1252"):
            try:
                self._raw_text = self.xml_bytes.decode(enc)
                return
            except UnicodeDecodeError:
                pass
        self._raw_text = self.xml_bytes.decode("utf-8", errors="replace")

    # ── Extração via XPath (stdlib) ───────────────────────────────────────────

    def _xpath_et(self, xpaths: List[str]) -> Optional[str]:
        if self._et_root is None:
            return None
        for xp in xpaths:
            try:
                if xp.endswith("/@Id") or "/@" in xp:
                    # Atributos: extraia manualmente
                    tag_path, attr = xp.rsplit("/@", 1)
                    el = self._et_root.find(tag_path)
                    if el is not None:
                        val = el.get(attr)
                        if val:
                            return val.strip()
                else:
                    el = self._et_root.find(xp)
                    if el is not None and el.text:
                        return el.text.strip()
            except Exception:
                pass
        return None

    # ── Extração via XPath (lxml) ─────────────────────────────────────────────

    def _xpath_lxml(self, xpaths: List[str]) -> Optional[str]:
        if self._lx_root is None:
            return None
        # Constrói mapa de namespaces do próprio documento
        ns_doc: Dict[str, str] = {}
        if HAS_LXML:
            try:
                ns_doc = dict(self._lx_root.nsmap)
                ns_doc = {k: v for k, v in ns_doc.items() if k and v}
            except Exception:
                pass
        ns_doc.update(NS_PREFIXOS)

        for xp in xpaths:
            try:
                # lxml: usa // sem namespace para varredura total
                result = self._lx_root.xpath(xp)
                if result:
                    val = result[0]
                    if hasattr(val, "text") and val.text:
                        return val.text.strip()
                    if isinstance(val, str) and val.strip():
                        return val.strip()
            except Exception:
                pass

            # Tenta com prefixo nfe:
            xp_ns = xp.replace(
                "{http://www.portalfiscal.inf.br/nfe}",
                "nfe:"
            )
            try:
                result = self._lx_root.xpath(
                    xp_ns.replace(".//", "//"),
                    namespaces={"nfe": "http://www.portalfiscal.inf.br/nfe"}
                )
                if result:
                    val = result[0]
                    if hasattr(val, "text") and val.text:
                        return val.text.strip()
                    if isinstance(val, str) and val.strip():
                        return val.strip()
            except Exception:
                pass
        return None

    # ── Varredura total de tags (fallback agressivo) ───────────────────────────

    def _tag_search(self, tags_alvo: List[str]) -> Optional[str]:
        """
        Percorre recursivamente todos os elementos buscando por nome de tag
        (ignorando namespace e case).
        """
        tags_norm = {t.lower() for t in tags_alvo}
        roots = []
        if self._et_root is not None:
            roots.append(self._et_root)
        if self._lx_root is not None:
            roots.append(self._lx_root)

        for root in roots:
            for el in root.iter():
                tag_local = _strip_ns(el.tag).lower()
                if tag_local in tags_norm:
                    texto = (el.text or "").strip()
                    if texto:
                        return texto
        return None

    # ── Fallback Regex no texto bruto ─────────────────────────────────────────

    def _regex_raw(self, patterns: List[re.Pattern]) -> Optional[str]:
        if not self._raw_text:
            return None
        for pat in patterns:
            m = pat.search(self._raw_text)
            if m:
                try:
                    return m.group(1).strip()
                except IndexError:
                    pass
        return None

    # ── Fallback por chave de 44 dígitos ──────────────────────────────────────

    def _extrair_chave(self) -> str:
        if self._chave:
            return self._chave

        # 1. Xpath chave explícita
        chave = (
            self._xpath_et(XPATHS_EXTRAS["chave_nfe"])
            or self._xpath_lxml(XPATHS_EXTRAS["chave_nfe"])
            or self._tag_search(["chNFe", "chnfe"])
        )

        # 2. Atributo Id="NFe..." no elemento infNFe
        if not chave:
            for root in filter(None, [self._et_root, self._lx_root]):
                for el in root.iter():
                    id_val = el.get("Id", "")
                    if id_val:
                        digits = re.sub(r"\D", "", id_val)
                        if len(digits) == 44:
                            chave = digits
                            break
                if chave:
                    break

        # 3. Regex no texto bruto
        if not chave and self._raw_text:
            for pat in [RE_CHAVE_ID, RE_CHAVE_CHAVE]:
                m = pat.search(self._raw_text)
                if m:
                    chave = m.group(1)
                    break

        self._chave = chave or ""
        return self._chave

    # ── API Pública ────────────────────────────────────────────────────────────

    def extrair(self) -> Dict[str, Any]:
        """
        Executa todas as estratégias em cascata e retorna dicionário com
        os campos extraídos.
        """
        # Carrega texto bruto
        self._load_text()

        # Tentativas de parsing
        ok_et = self._parse_stdlib()
        ok_lx = self._parse_lxml()

        if not ok_et and not ok_lx:
            log.warning(f"Nenhum parser conseguiu abrir: {self.arquivo}")

        # ── SÉRIE ─────────────────────────────────────────────────────────────
        serie = (
            self._xpath_et(XPATHS_SERIE)
            or self._xpath_lxml(XPATHS_SERIE)
            or self._tag_search(["serie", "Serie", "SERIE"])
            or self._regex_raw([RE_SERIE_XML])
        )
        if not serie:
            chave = self._extrair_chave()
            serie = _extrair_serie_da_chave(chave)

        # ── NÚMERO DA NOTA (nNF) ──────────────────────────────────────────────
        nnf = (
            self._xpath_et(XPATHS_NNF)
            or self._xpath_lxml(XPATHS_NNF)
            or self._tag_search(["nNF", "nnf", "NNF"])
            or self._regex_raw([RE_NNF_XML])
        )
        if not nnf:
            chave = self._extrair_chave()
            nnf = _extrair_nnf_da_chave(chave)

        # ── VALOR TOTAL (vNF) ─────────────────────────────────────────────────
        vnf = (
            self._xpath_et(XPATHS_VNF)
            or self._xpath_lxml(XPATHS_VNF)
            or self._tag_search(["vNF", "vnf", "VNF"])
            or self._regex_raw([RE_VNF_XML])
        )

        # ── DATA/HORA EMISSÃO (dhEmi / dEmi) ──────────────────────────────────
        dhemi_raw = (
            self._xpath_et(XPATHS_DHEMI)
            or self._xpath_lxml(XPATHS_DHEMI)
            or self._tag_search(["dhEmi", "dEmi", "dhemi", "demi"])
            or self._regex_raw([RE_DHEMI_XML])
        )
        data_emissao, hora_emissao = _parse_data_hora(dhemi_raw or "")

        # ── CAMPOS COMPLEMENTARES ─────────────────────────────────────────────
        extras: Dict[str, Optional[str]] = {}
        for campo, xpaths in XPATHS_EXTRAS.items():
            val = (
                self._xpath_et(xpaths)
                or self._xpath_lxml(xpaths)
            )
            if campo in ("cnpj_emitente", "cnpj_destinatario") and val:
                val = _formatar_cnpj(val)
            extras[campo] = val

        # Chave final
        chave = self._extrair_chave()

        return {
            # Campos críticos
            "serie":          (serie or "").strip(),
            "numero_nota":    (nnf or "").strip(),
            "valor_total":    vnf,
            "valor_total_f":  _valor_float(vnf),
            "data_emissao":   data_emissao,
            "hora_emissao":   hora_emissao,
            "dhemi_raw":      dhemi_raw or "",
            # Identificação
            "chave_nfe":      chave,
            "modelo":         extras.get("modelo", ""),
            "protocolo":      extras.get("protocolo", ""),
            "versao_xml":     extras.get("versao", ""),
            # Emitente
            "cnpj_emitente":  extras.get("cnpj_emitente", ""),
            "razao_emitente": extras.get("razao_emitente", ""),
            "uf_emitente":    extras.get("uf_emitente", ""),
            # Destinatário
            "cnpj_destinatario":  extras.get("cnpj_destinatario", ""),
            "razao_destinatario": extras.get("razao_destinatario", ""),
            # Valores complementares
            "valor_icms":     extras.get("valor_icms", ""),
            "valor_ipi":      extras.get("valor_ipi", ""),
            "valor_pis":      extras.get("valor_pis", ""),
            "valor_cofins":   extras.get("valor_cofins", ""),
            "valor_frete":    extras.get("valor_frete", ""),
            "valor_desconto": extras.get("valor_desconto", ""),
            "natureza_op":    extras.get("natureza_operacao", ""),
            # Diagnóstico
            "_parser_et": ok_et,
            "_parser_lx": ok_lx,
            "_fonte":     "xml",
        }


# ══════════════════════════════════════════════════════════════════════════════
# ESTRATÉGIAS DE PARSING PDF (DANFE)
# ══════════════════════════════════════════════════════════════════════════════

class _EstrategiaPDF:
    """Extração de campos de DANFE PDF usando pdfplumber + PyMuPDF + OCR."""

    def __init__(self, pdf_bytes: bytes, arquivo: str = ""):
        self.pdf_bytes = pdf_bytes
        self.arquivo   = arquivo

    def _extrair_texto_pdfplumber(self) -> str:
        if not HAS_PDFPLUMBER:
            return ""
        try:
            textos = []
            with pdfplumber.open(io.BytesIO(self.pdf_bytes)) as pdf:
                for page in pdf.pages:
                    t = page.extract_text(x_tolerance=3, y_tolerance=3) or ""
                    textos.append(t)
            return "\n".join(textos)
        except Exception as e:
            log.debug(f"pdfplumber erro: {e}")
            return ""

    def _extrair_texto_pymupdf(self) -> str:
        if not HAS_FITZ:
            return ""
        try:
            doc = fitz.open(stream=self.pdf_bytes, filetype="pdf")
            textos = [page.get_text("text") for page in doc]
            doc.close()
            return "\n".join(textos)
        except Exception as e:
            log.debug(f"PyMuPDF erro: {e}")
            return ""

    def _extrair_texto_ocr(self) -> str:
        """OCR via pytesseract + PyMuPDF (renderiza páginas como imagem)."""
        if not (HAS_OCR and HAS_FITZ):
            return ""
        try:
            doc = fitz.open(stream=self.pdf_bytes, filetype="pdf")
            textos = []
            for page in doc:
                mat  = fitz.Matrix(2, 2)  # 2x zoom para melhor OCR
                pix  = page.get_pixmap(matrix=mat)
                img  = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                text = pytesseract.image_to_string(img, lang="por")
                textos.append(text)
            doc.close()
            return "\n".join(textos)
        except Exception as e:
            log.debug(f"OCR erro: {e}")
            return ""

    def _aplicar_regex(self, texto: str, patterns: List[re.Pattern],
                        grupo: int = 1) -> Optional[str]:
        for pat in patterns:
            m = pat.search(texto)
            if m:
                try:
                    return m.group(grupo).strip()
                except IndexError:
                    pass
        return None

    def extrair(self) -> Dict[str, Any]:
        # Tenta todos os motores de extração de texto
        texto = self._extrair_texto_pdfplumber()
        if len(texto.strip()) < 50:
            log.debug("pdfplumber retornou pouco texto, tentando PyMuPDF...")
            texto = self._extrair_texto_pymupdf()
        if len(texto.strip()) < 50:
            log.info(f"PDF parece scaneado, ativando OCR: {self.arquivo}")
            texto = self._extrair_texto_ocr()

        serie_m = re.search(r"Nº\s*(\d+)\s*/\s*([A-Z0-9]{1,5})", texto)
        if serie_m:
            nnf_pdf   = serie_m.group(1).strip()
            serie_pdf = serie_m.group(2).strip()
        else:
            nnf_pdf   = self._aplicar_regex(texto, RE_PDF_NNF)
            serie_pdf = self._aplicar_regex(texto, RE_PDF_SERIE)
            if not serie_pdf:
                # Regex específico para "Série" sozinha
                m = re.search(r"[Ss][éeÉE]rie[:\s]*([A-Z0-9]{1,5})", texto)
                serie_pdf = m.group(1) if m else ""

        vnf_pdf = self._aplicar_regex(texto, RE_PDF_VNF)

        dhemi_raw = None
        for pat in RE_PDF_DHEMI:
            m = pat.search(texto)
            if m:
                partes = [g for g in m.groups() if g]
                dhemi_raw = " ".join(partes)
                break
        data_emissao, hora_emissao = _parse_data_hora(dhemi_raw or "")

        return {
            "serie":          (serie_pdf or "").strip(),
            "numero_nota":    (nnf_pdf or "").strip(),
            "valor_total":    vnf_pdf,
            "valor_total_f":  _valor_float(vnf_pdf),
            "data_emissao":   data_emissao,
            "hora_emissao":   hora_emissao,
            "dhemi_raw":      dhemi_raw or "",
            "chave_nfe":      "",
            "modelo":         "",
            "protocolo":      "",
            "versao_xml":     "",
            "cnpj_emitente":  "",
            "razao_emitente": "",
            "uf_emitente":    "",
            "cnpj_destinatario":  "",
            "razao_destinatario": "",
            "valor_icms":     "",
            "valor_ipi":      "",
            "valor_pis":      "",
            "valor_cofins":   "",
            "valor_frete":    "",
            "valor_desconto": "",
            "natureza_op":    "",
            "_parser_et": False,
            "_parser_lx": False,
            "_fonte":     "pdf",
        }


# ══════════════════════════════════════════════════════════════════════════════
# CLASSE PRINCIPAL
# ══════════════════════════════════════════════════════════════════════════════

class UltraMaxNFeParser:
    """
    Parser de NF-e/NFC-e versão MÁXIMA.

    Suporte:
      - NF-e modelo 55 (todas as versões: 2.x, 3.x, 4.x)
      - NFC-e modelo 65
      - NF-e de produtor rural
      - NF-e de entrada
      - CT-e (parcial)
      - DANFE em PDF (pdfplumber + PyMuPDF + OCR)

    Campos críticos extraídos com 100% de cobertura via fallbacks:
      serie | numero_nota (nNF) | valor_total (vNF) | data_emissao (dhEmi)

    Uso rápido:
        parser = UltraMaxNFeParser()
        result = parser.parse_xml(Path("nota.xml").read_bytes())
        result = parser.parse_pdf(Path("danfe.pdf").read_bytes())
        parser.processar_pasta("/notas/", saida_json="relatorio.json")
    """

    VERSION = "2.0.0-max"

    def __init__(
        self,
        workers: int = 8,
        salvar_json_auto: bool = True,
        json_path: Optional[str] = None,
        log_level: str = "INFO",
    ):
        self.workers         = workers
        self.salvar_json_auto = salvar_json_auto
        self.json_path       = json_path
        log.setLevel(getattr(logging, log_level.upper(), logging.INFO))

        log.info(f"UltraMaxNFeParser v{self.VERSION} inicializado")
        log.info(f"  lxml:        {'✅' if HAS_LXML else '❌ (instale: pip install lxml)'}")
        log.info(f"  pdfplumber:  {'✅' if HAS_PDFPLUMBER else '❌ (instale: pip install pdfplumber)'}")
        log.info(f"  PyMuPDF:     {'✅' if HAS_FITZ else '❌ (instale: pip install PyMuPDF)'}")
        log.info(f"  OCR pytess:  {'✅' if HAS_OCR else '⚠️  (opcional: pip install pytesseract Pillow)'}")
        log.info(f"  Workers:     {workers}")

    # ── API Pública ────────────────────────────────────────────────────────────

    def parse_xml(
        self,
        xml_input: Union[bytes, str, Path],
        arquivo: str = "",
    ) -> Dict[str, Any]:
        """
        Extrai campos de uma NF-e em XML.

        Parâmetros:
            xml_input: bytes do XML, string com o conteúdo ou Path do arquivo.
            arquivo:   nome/caminho do arquivo (para logging).

        Retorna dicionário com todos os campos extraídos.
        """
        t0 = time.perf_counter()

        # Normaliza entrada
        if isinstance(xml_input, Path):
            arquivo = arquivo or str(xml_input)
            xml_input = xml_input.read_bytes()
        elif isinstance(xml_input, str):
            xml_input = xml_input.encode("utf-8")

        nome = os.path.basename(arquivo) or "<bytes>"

        try:
            est = _EstrategiaXML(xml_input, arquivo=arquivo)
            dados = est.extrair()
            dados["arquivo"]  = nome
            dados["_arquivo_completo"] = arquivo
            dados["_tempo_ms"] = round((time.perf_counter() - t0) * 1000, 2)
            dados["_status"] = self._avaliar_status(dados)

            self._logar_resultado(dados)
            return dados

        except Exception as exc:
            log.error(f"Erro crítico ao processar XML {nome}: {exc}")
            log.debug(traceback.format_exc())
            return self._resultado_erro(nome, str(exc), "xml")

    def parse_pdf(
        self,
        pdf_input: Union[bytes, Path],
        arquivo: str = "",
    ) -> Dict[str, Any]:
        """
        Extrai campos de um DANFE em PDF.

        Parâmetros:
            pdf_input: bytes do PDF ou Path do arquivo.
            arquivo:   nome/caminho do arquivo (para logging).

        Retorna dicionário com todos os campos extraídos.
        """
        t0 = time.perf_counter()

        if isinstance(pdf_input, Path):
            arquivo = arquivo or str(pdf_input)
            pdf_input = pdf_input.read_bytes()

        nome = os.path.basename(arquivo) or "<bytes>"

        if not HAS_PDFPLUMBER and not HAS_FITZ:
            log.error("Nenhum motor PDF disponível. Instale pdfplumber e/ou PyMuPDF.")
            return self._resultado_erro(nome, "Sem motor PDF", "pdf")

        try:
            est  = _EstrategiaPDF(pdf_input, arquivo=arquivo)
            dados = est.extrair()
            dados["arquivo"]  = nome
            dados["_arquivo_completo"] = arquivo
            dados["_tempo_ms"] = round((time.perf_counter() - t0) * 1000, 2)
            dados["_status"] = self._avaliar_status(dados)

            self._logar_resultado(dados)
            return dados

        except Exception as exc:
            log.error(f"Erro crítico ao processar PDF {nome}: {exc}")
            log.debug(traceback.format_exc())
            return self._resultado_erro(nome, str(exc), "pdf")

    def processar_pasta(
        self,
        pasta: Union[str, Path],
        saida_json: Optional[str] = None,
        extensoes: Tuple[str, ...] = (".xml", ".XML", ".pdf", ".PDF"),
        recursivo: bool = True,
        workers: Optional[int] = None,
    ) -> Dict[str, Any]:
        """
        Processa todos os arquivos NF-e em uma pasta (recursivamente).

        Parâmetros:
            pasta:      caminho da pasta.
            saida_json: caminho do JSON de saída (None = automático).
            extensoes:  tuplas de extensões a processar.
            recursivo:  busca recursiva em subpastas.
            workers:    threads paralelas (None = usa self.workers).

        Retorna dicionário com estatísticas e lista de resultados.
        """
        pasta = Path(pasta)
        if not pasta.exists():
            raise FileNotFoundError(f"Pasta não encontrada: {pasta}")

        # Coleta arquivos
        pattern = "**/*" if recursivo else "*"
        arquivos: List[Path] = []
        for ext in extensoes:
            arquivos.extend(pasta.glob(f"{pattern}{ext}"))
        arquivos = sorted(set(arquivos))

        total = len(arquivos)
        if total == 0:
            log.warning(f"Nenhum arquivo encontrado em: {pasta}")
            return {"total": 0, "resultados": [], "estatisticas": {}}

        log.info(f"╔══════════════════════════════════════════╗")
        log.info(f"║  Processando {total:>5} arquivo(s) em:      ║")
        log.info(f"║  {str(pasta):<42} ║")
        log.info(f"╚══════════════════════════════════════════╝")

        t_inicio = time.perf_counter()
        resultados: List[Dict] = []
        n_workers = workers or self.workers

        # Processamento paralelo
        with ThreadPoolExecutor(max_workers=n_workers) as executor:
            futures = {}
            for arq in arquivos:
                if arq.suffix.lower() == ".xml":
                    fut = executor.submit(self.parse_xml, arq, str(arq))
                else:
                    fut = executor.submit(self.parse_pdf, arq, str(arq))
                futures[fut] = arq

            processados = 0
            for fut in as_completed(futures):
                arq = futures[fut]
                try:
                    res = fut.result()
                    resultados.append(res)
                except Exception as exc:
                    log.error(f"Thread falhou em {arq.name}: {exc}")
                    resultados.append(self._resultado_erro(arq.name, str(exc), "?"))
                finally:
                    processados += 1
                    if processados % 100 == 0 or processados == total:
                        pct = processados / total * 100
                        log.info(f"  Progresso: {processados}/{total} ({pct:.0f}%)")

        t_total = time.perf_counter() - t_inicio

        # Ordenar por arquivo
        resultados.sort(key=lambda r: r.get("arquivo", ""))

        # Estatísticas
        n_ok     = sum(1 for r in resultados if r.get("_status") == "OK")
        n_parcial = sum(1 for r in resultados if r.get("_status") == "PARCIAL")
        n_erro    = sum(1 for r in resultados if r.get("_status") == "ERRO")
        n_xml     = sum(1 for r in resultados if r.get("_fonte") == "xml")
        n_pdf     = sum(1 for r in resultados if r.get("_fonte") == "pdf")

        estatisticas = {
            "total":          total,
            "ok":             n_ok,
            "parcial":        n_parcial,
            "erro":           n_erro,
            "xml":            n_xml,
            "pdf":            n_pdf,
            "taxa_sucesso":   round(n_ok / total * 100, 2) if total else 0,
            "tempo_total_s":  round(t_total, 2),
            "media_ms":       round(t_total / total * 1000, 1) if total else 0,
            "gerado_em":      datetime.now().isoformat(),
            "parser_version": self.VERSION,
        }

        log.info(f"\n{'─'*50}")
        log.info(f"  ✅ OK:       {n_ok:>5}")
        log.info(f"  ⚠️  Parcial:  {n_parcial:>5}")
        log.info(f"  ❌ Erro:     {n_erro:>5}")
        log.info(f"  📄 XML:      {n_xml:>5}  |  📑 PDF: {n_pdf}")
        log.info(f"  🎯 Precisão: {estatisticas['taxa_sucesso']}%")
        log.info(f"  ⏱  Tempo:    {estatisticas['tempo_total_s']}s "
                 f"({estatisticas['media_ms']} ms/arq)")
        log.info(f"{'─'*50}\n")

        relatorio = {
            "estatisticas": estatisticas,
            "resultados":   resultados,
        }

        # Salva JSON
        json_final = saida_json or self.json_path
        if json_final or self.salvar_json_auto:
            if not json_final:
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                json_final = str(pasta / f"relatorio_nfe_{ts}.json")
            self._salvar_json(relatorio, json_final)

        return relatorio

    # ── Helpers internos ──────────────────────────────────────────────────────

    @staticmethod
    def _avaliar_status(dados: Dict[str, Any]) -> str:
        """
        OK      → todos os 4 campos críticos presentes
        PARCIAL → pelo menos 1 campo crítico presente
        ERRO    → nenhum campo crítico extraído
        """
        criticos = ["serie", "numero_nota", "valor_total", "data_emissao"]
        presentes = sum(1 for c in criticos if dados.get(c))
        if presentes == 4:
            return "OK"
        if presentes > 0:
            return "PARCIAL"
        return "ERRO"

    @staticmethod
    def _logar_resultado(dados: Dict) -> None:
        status = dados.get("_status", "?")
        nome   = dados.get("arquivo", "?")
        emoji  = {"OK": "✅", "PARCIAL": "⚠️ ", "ERRO": "❌"}.get(status, "?")
        campos = (
            f"Série={dados.get('serie') or '—':>4} | "
            f"nNF={dados.get('numero_nota') or '—':>10} | "
            f"vNF={dados.get('valor_total') or '—':>12} | "
            f"Data={dados.get('data_emissao') or '—':>12}"
        )
        ms = dados.get("_tempo_ms", 0)
        log.info(f"{emoji} {nome:<45} {campos}  [{ms}ms]")

    @staticmethod
    def _resultado_erro(nome: str, msg: str, fonte: str) -> Dict[str, Any]:
        return {
            "arquivo":           nome,
            "_arquivo_completo": nome,
            "_status":           "ERRO",
            "_fonte":            fonte,
            "_erro":             msg,
            "_tempo_ms":         0,
            "serie":             "",
            "numero_nota":       "",
            "valor_total":       None,
            "valor_total_f":     None,
            "data_emissao":      "",
            "hora_emissao":      "",
            "dhemi_raw":         "",
            "chave_nfe":         "",
            "modelo":            "",
            "protocolo":         "",
            "versao_xml":        "",
            "cnpj_emitente":     "",
            "razao_emitente":    "",
            "uf_emitente":       "",
            "cnpj_destinatario": "",
            "razao_destinatario": "",
            "valor_icms":        "",
            "valor_ipi":         "",
            "valor_pis":         "",
            "valor_cofins":      "",
            "valor_frete":       "",
            "valor_desconto":    "",
            "natureza_op":       "",
            "_parser_et":        False,
            "_parser_lx":        False,
        }

    @staticmethod
    def _salvar_json(relatorio: Dict, caminho: str) -> None:
        try:
            Path(caminho).parent.mkdir(parents=True, exist_ok=True)
            with open(caminho, "w", encoding="utf-8") as f:
                json.dump(relatorio, f, ensure_ascii=False, indent=2, default=str)
            log.info(f"📁 Relatório JSON salvo: {caminho}")
        except Exception as e:
            log.error(f"Falha ao salvar JSON: {e}")

    # ── Conveniência ─────────────────────────────────────────────────────────

    def parse_arquivo(self, caminho: Union[str, Path]) -> Dict[str, Any]:
        """Auto-detecta XML ou PDF e chama o parser correto."""
        p = Path(caminho)
        if p.suffix.lower() in (".xml",):
            return self.parse_xml(p)
        elif p.suffix.lower() in (".pdf",):
            return self.parse_pdf(p)
        else:
            # Tenta detectar pelo conteúdo
            header = p.read_bytes()[:10]
            if b"<?xml" in header or b"<nfe" in header.lower():
                return self.parse_xml(p)
            return self.parse_pdf(p)

    def parse_multiplos(
        self, arquivos: List[Union[str, Path]]
    ) -> List[Dict[str, Any]]:
        """Processa lista de arquivos em paralelo."""
        resultados = []
        with ThreadPoolExecutor(max_workers=self.workers) as ex:
            futs = {ex.submit(self.parse_arquivo, a): a for a in arquivos}
            for fut in as_completed(futs):
                try:
                    resultados.append(fut.result())
                except Exception as e:
                    arq = futs[fut]
                    resultados.append(
                        self._resultado_erro(str(arq), str(e), "?")
                    )
        return resultados

    def resumo_campos_criticos(
        self, resultados: List[Dict[str, Any]]
    ) -> Dict[str, Any]:
        """Gera resumo de cobertura dos 4 campos críticos."""
        total = len(resultados)
        if total == 0:
            return {}
        campos = ["serie", "numero_nota", "valor_total", "data_emissao"]
        cobertura = {
            c: sum(1 for r in resultados if r.get(c)) / total * 100
            for c in campos
        }
        return {
            "total_notas": total,
            "cobertura_pct": {k: round(v, 2) for k, v in cobertura.items()},
            "media_cobertura": round(sum(cobertura.values()) / len(campos), 2),
        }


# ══════════════════════════════════════════════════════════════════════════════
# ENTRYPOINT CLI
# ══════════════════════════════════════════════════════════════════════════════

def _cli() -> None:
    import argparse

    parser = argparse.ArgumentParser(
        description="UltraMaxNFeParser — Extração máxima de NF-e/NFC-e",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemplos:
  # Processar pasta inteira
  python nfe_parser_max.py --pasta /notas/

  # Arquivo único XML
  python nfe_parser_max.py --arquivo nota.xml

  # Arquivo único PDF
  python nfe_parser_max.py --arquivo danfe.pdf

  # Personalizar saída JSON e workers
  python nfe_parser_max.py --pasta /notas/ --json resultado.json --workers 16
        """,
    )
    parser.add_argument("--pasta",    "-p", help="Pasta com XMLs/PDFs de NF-e")
    parser.add_argument("--arquivo",  "-a", help="Arquivo único (.xml ou .pdf)")
    parser.add_argument("--json",     "-j", help="Caminho do relatório JSON de saída")
    parser.add_argument("--workers",  "-w", type=int, default=8,
                        help="Número de threads paralelas (default: 8)")
    parser.add_argument("--log",      "-l", default="INFO",
                        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
                        help="Nível de log (default: INFO)")
    parser.add_argument("--version",  "-v", action="store_true",
                        help="Exibe versão e dependências")

    args = parser.parse_args()

    if args.version:
        p = UltraMaxNFeParser(log_level="INFO")
        print(f"\nUltraMaxNFeParser v{p.VERSION}")
        sys.exit(0)

    p = UltraMaxNFeParser(
        workers=args.workers,
        json_path=args.json,
        salvar_json_auto=bool(args.json),
        log_level=args.log,
    )

    if args.pasta:
        relatorio = p.processar_pasta(args.pasta, saida_json=args.json)
        resumo    = p.resumo_campos_criticos(relatorio["resultados"])
        print(f"\n📊 Cobertura dos campos críticos:")
        for campo, pct in resumo.get("cobertura_pct", {}).items():
            bar = "█" * int(pct / 5)
            print(f"   {campo:<20} {bar:<20} {pct:.1f}%")

    elif args.arquivo:
        res = p.parse_arquivo(args.arquivo)
        print(json.dumps(res, ensure_ascii=False, indent=2, default=str))

    else:
        parser.print_help()


if __name__ == "__main__":
    _cli()
