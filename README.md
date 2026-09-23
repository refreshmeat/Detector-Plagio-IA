# Detector de Plágio e IA

Aplicativo desktop em Python para análise local de textos, com duas frentes principais:

- **similaridade/plágio na web**, buscando evidências textuais em fontes públicas;
- **estimativa de autoria por IA**, usando um classificador local treinado para PT-BR.

O projeto foi criado para uso pessoal e como experimento de análise textual. Ele aceita texto colado e arquivos `.pdf`, `.docx`, `.txt` e `.md`, e pode gerar relatório em PDF.

## Principais recursos

- Interface desktop com Tkinter
- Extração de texto de PDF, DOCX, TXT e Markdown
- Busca de trechos semelhantes na web
- Comparação textual por similaridade
- Remoção/isolamento de referências e citações antes da análise autoral
- Classificador local de indícios de texto gerado por IA
- Calibração local
- Geração de relatório em PDF
- Processamento local dos arquivos enviados pelo usuário

## Stack

- Python 3
- Tkinter
- Requests + BeautifulSoup
- pypdf
- ReportLab
- scikit-learn + joblib

## Estrutura

```text
detector-plagio-ia-local/
├── detector_app.py
├── ai_detector_model.joblib
├── ai_detector_meta.json
├── requirements.txt
└── README.md
```

## Como executar

```bash
python -m venv .venv
.venv\Scripts\activate
pip install -r requirements.txt
python detector_app.py
```

## Observação sobre detecção de IA

Detectores de autoria por IA são **estimativas probabilísticas**, não provas. O resultado deste software deve ser interpretado como um indício auxiliar e não como evidência definitiva para decisões acadêmicas, disciplinares ou profissionais.

## Privacidade

Os arquivos analisados não são enviados para uma API proprietária de IA. A etapa de comparação de similaridade pode realizar consultas públicas na web para localizar possíveis correspondências.

## Status

Projeto funcional em desenvolvimento contínuo, criado originalmente para uso pessoal e publicado como demonstração de engenharia de software, processamento de texto e machine learning aplicado.
