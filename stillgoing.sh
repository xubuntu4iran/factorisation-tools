 for u in *gpl; do [ -s $u ] && echo $u $(tail -n 2 $u | head -n 1) $(tail -n 1 $u) $(ps aux | grep aliquot | grep ${u%.gpl}); done | awk '{print $5-$3,$0}' | sort -g
