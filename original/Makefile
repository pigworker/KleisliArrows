default : Kleisli.ps

Kleisli.tex : Kleisli.lhs
	lhs2TeX --poly Kleisli.lhs > Kleisli.tex

Kleisli.aux : Kleisli.tex
	latex Kleisli

Kleisli.bbl : Kleisli.bib Kleisli.aux
	bibtex Kleisli

Kleisli.dvi : Kleisli.tex Kleisli.bbl
	latex Kleisli
	latex Kleisli

Kleisli.ps : Kleisli.dvi
	dvips -P cmz -t letter -o Kleisli.ps Kleisli.dvi

Kleisli.pdf : Kleisli.ps
	ps2pdf Kleisli.ps Kleisli.pdf

