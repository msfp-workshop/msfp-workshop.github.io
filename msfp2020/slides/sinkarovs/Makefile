

all: present.html

_build/%.md: %.lagda.md
	agda --html-highlight=auto --html --html-dir=_build $<

%.html: _build/%.md ./reveal.js
	pandoc -t revealjs \
               -V theme=white \
               --slide-level=2 \
               --css=Agda.css --css=my.css -s $< -o $@

# XXX since version 4.0 the paths in the library do not match
# the paths that pandoc generates.  FUCK YOU, STUPID PIECE OF
# SHIT!
#./reveal.js:
#	git clone https://github.com/hakimel/reveal.js

