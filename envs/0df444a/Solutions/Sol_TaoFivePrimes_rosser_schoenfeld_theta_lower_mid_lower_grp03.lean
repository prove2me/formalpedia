-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:29:57.063033+00:00
-- url     : https://prove2.me/submissions/da30c86e-f863-4ab1-a661-bfd1520ab850

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert102
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert103
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert104
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert105
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert106
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert107
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert108
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert109
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert110
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert111
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert112
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert113
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert114
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert115
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert116
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert117
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert118
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert119
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert120
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert121
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert122
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert123
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert124
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert125
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert126
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert127
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert128
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert129
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert130
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert131
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert132
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert133
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert134
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert135
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert136
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert137
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert138
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert139
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert140
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert141
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert142
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert143
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert144
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert145
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert146
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert147
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert148
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert149
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert150
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert151

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03` (the range 693190904 <= n <= 1000000000 with its carry in and carry out) from the 50 Phase 1 certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert102` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert151`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real))
    (n : Nat) (h1 : 693190904 <= n) (h2 : n <= 1000000000) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real)) := by
  have hb0 := hbase
  have hb1 : (768820175898222834044 : Real) / 2 ^ 40 <= Chebyshev.theta (699268608 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert102 hb0 693190904 le_rfl (by norm_num)).2
  have hb2 : (775507537898463962466 : Real) / 2 ^ 40 <= Chebyshev.theta (705351204 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert103 hb1 699268608 le_rfl (by norm_num)).2
  have hb3 : (782197731126421227288 : Real) / 2 ^ 40 <= Chebyshev.theta (711434862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert104 hb2 705351204 le_rfl (by norm_num)).2
  have hb4 : (788890733729285756594 : Real) / 2 ^ 40 <= Chebyshev.theta (717526298 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert105 hb3 711434862 le_rfl (by norm_num)).2
  have hb5 : (795586522840378970913 : Real) / 2 ^ 40 <= Chebyshev.theta (723611424 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert106 hb4 717526298 le_rfl (by norm_num)).2
  have hb6 : (802285074278471091679 : Real) / 2 ^ 40 <= Chebyshev.theta (729708912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert107 hb5 723611424 le_rfl (by norm_num)).2
  have hb7 : (808986370222787851985 : Real) / 2 ^ 40 <= Chebyshev.theta (735806570 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert108 hb6 729708912 le_rfl (by norm_num)).2
  have hb8 : (815690386139319703486 : Real) / 2 ^ 40 <= Chebyshev.theta (741897012 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert109 hb7 735806570 le_rfl (by norm_num)).2
  have hb9 : (822397100049477645378 : Real) / 2 ^ 40 <= Chebyshev.theta (748005188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert110 hb8 741897012 le_rfl (by norm_num)).2
  have hb10 : (829106495157148904514 : Real) / 2 ^ 40 <= Chebyshev.theta (754116218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert111 hb9 748005188 le_rfl (by norm_num)).2
  have hb11 : (835818547468657503982 : Real) / 2 ^ 40 <= Chebyshev.theta (760217454 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert112 hb10 754116218 le_rfl (by norm_num)).2
  have hb12 : (842533237546694029282 : Real) / 2 ^ 40 <= Chebyshev.theta (766331430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert113 hb11 760217454 le_rfl (by norm_num)).2
  have hb13 : (849250545549257083177 : Real) / 2 ^ 40 <= Chebyshev.theta (772433478 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert114 hb12 766331430 le_rfl (by norm_num)).2
  have hb14 : (855970449734618765565 : Real) / 2 ^ 40 <= Chebyshev.theta (778549394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert115 hb13 772433478 le_rfl (by norm_num)).2
  have hb15 : (862692931825214548563 : Real) / 2 ^ 40 <= Chebyshev.theta (784659612 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert116 hb14 778549394 le_rfl (by norm_num)).2
  have hb16 : (869417970112622217083 : Real) / 2 ^ 40 <= Chebyshev.theta (790765920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert117 hb15 784659612 le_rfl (by norm_num)).2
  have hb17 : (876145546815327278175 : Real) / 2 ^ 40 <= Chebyshev.theta (796888034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert118 hb16 790765920 le_rfl (by norm_num)).2
  have hb18 : (882875643577989917160 : Real) / 2 ^ 40 <= Chebyshev.theta (803009258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert119 hb17 796888034 le_rfl (by norm_num)).2
  have hb19 : (889608243169104607049 : Real) / 2 ^ 40 <= Chebyshev.theta (809125862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert120 hb18 803009258 le_rfl (by norm_num)).2
  have hb20 : (896343326845943621413 : Real) / 2 ^ 40 <= Chebyshev.theta (815255994 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert121 hb19 809125862 le_rfl (by norm_num)).2
  have hb21 : (903080877159491121623 : Real) / 2 ^ 40 <= Chebyshev.theta (821378672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert122 hb20 815255994 le_rfl (by norm_num)).2
  have hb22 : (909820878057709386928 : Real) / 2 ^ 40 <= Chebyshev.theta (827510988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert123 hb21 821378672 le_rfl (by norm_num)).2
  have hb23 : (916563311903656646484 : Real) / 2 ^ 40 <= Chebyshev.theta (833642058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert124 hb22 827510988 le_rfl (by norm_num)).2
  have hb24 : (923308160330829168848 : Real) / 2 ^ 40 <= Chebyshev.theta (839774562 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert125 hb23 833642058 le_rfl (by norm_num)).2
  have hb25 : (930055406383098040572 : Real) / 2 ^ 40 <= Chebyshev.theta (845911358 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert126 hb24 839774562 le_rfl (by norm_num)).2
  have hb26 : (936805035183985976272 : Real) / 2 ^ 40 <= Chebyshev.theta (852054188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert127 hb25 845911358 le_rfl (by norm_num)).2
  have hb27 : (943557029663492111496 : Real) / 2 ^ 40 <= Chebyshev.theta (858192092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert128 hb26 852054188 le_rfl (by norm_num)).2
  have hb28 : (950311375719728919082 : Real) / 2 ^ 40 <= Chebyshev.theta (864342252 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert129 hb27 858192092 le_rfl (by norm_num)).2
  have hb29 : (957068055072340891957 : Real) / 2 ^ 40 <= Chebyshev.theta (870482720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert130 hb28 864342252 le_rfl (by norm_num)).2
  have hb30 : (963827052273630336921 : Real) / 2 ^ 40 <= Chebyshev.theta (876634988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert131 hb29 870482720 le_rfl (by norm_num)).2
  have hb31 : (970588354123940266716 : Real) / 2 ^ 40 <= Chebyshev.theta (882785598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert132 hb30 876634988 le_rfl (by norm_num)).2
  have hb32 : (977351944265527706504 : Real) / 2 ^ 40 <= Chebyshev.theta (888940590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert133 hb31 882785598 le_rfl (by norm_num)).2
  have hb33 : (984117807606823907894 : Real) / 2 ^ 40 <= Chebyshev.theta (895099244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert134 hb32 888940590 le_rfl (by norm_num)).2
  have hb34 : (990885929667298500107 : Real) / 2 ^ 40 <= Chebyshev.theta (901255308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert135 hb33 895099244 le_rfl (by norm_num)).2
  have hb35 : (997656295101403628344 : Real) / 2 ^ 40 <= Chebyshev.theta (907413294 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert136 hb34 901255308 le_rfl (by norm_num)).2
  have hb36 : (1004428885821919545570 : Real) / 2 ^ 40 <= Chebyshev.theta (913563882 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert137 hb35 907413294 le_rfl (by norm_num)).2
  have hb37 : (1011203688383024899854 : Real) / 2 ^ 40 <= Chebyshev.theta (919722338 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert138 hb36 913563882 le_rfl (by norm_num)).2
  have hb38 : (1017980689931330188935 : Real) / 2 ^ 40 <= Chebyshev.theta (925885824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert139 hb37 919722338 le_rfl (by norm_num)).2
  have hb39 : (1024759879293615383705 : Real) / 2 ^ 40 <= Chebyshev.theta (932059862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert140 hb38 925885824 le_rfl (by norm_num)).2
  have hb40 : (1031541241048790125923 : Real) / 2 ^ 40 <= Chebyshev.theta (938225552 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert141 hb39 932059862 le_rfl (by norm_num)).2
  have hb41 : (1038324762665729977281 : Real) / 2 ^ 40 <= Chebyshev.theta (944397662 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert142 hb40 938225552 le_rfl (by norm_num)).2
  have hb42 : (1045110429120593951097 : Real) / 2 ^ 40 <= Chebyshev.theta (950571314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert143 hb41 944397662 le_rfl (by norm_num)).2
  have hb43 : (1051898227664747297423 : Real) / 2 ^ 40 <= Chebyshev.theta (956743928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert144 hb42 950571314 le_rfl (by norm_num)).2
  have hb44 : (1058688142822024335308 : Real) / 2 ^ 40 <= Chebyshev.theta (962909808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert145 hb43 956743928 le_rfl (by norm_num)).2
  have hb45 : (1065480162958321338524 : Real) / 2 ^ 40 <= Chebyshev.theta (969088578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert146 hb44 962909808 le_rfl (by norm_num)).2
  have hb46 : (1072274276176252210466 : Real) / 2 ^ 40 <= Chebyshev.theta (975269910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert147 hb45 969088578 le_rfl (by norm_num)).2
  have hb47 : (1079070471680309439245 : Real) / 2 ^ 40 <= Chebyshev.theta (981454742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert148 hb46 975269910 le_rfl (by norm_num)).2
  have hb48 : (1085868734456141367430 : Real) / 2 ^ 40 <= Chebyshev.theta (987633810 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert149 hb47 981454742 le_rfl (by norm_num)).2
  have hb49 : (1092669051988066974905 : Real) / 2 ^ 40 <= Chebyshev.theta (993817664 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert150 hb48 987633810 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert151 hb49 993817664 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 845911358 with hc25 | hc25
  · rcases Nat.lt_or_ge n 766331430 with hc12 | hc12
    · rcases Nat.lt_or_ge n 729708912 with hc6 | hc6
      · rcases Nat.lt_or_ge n 711434862 with hc3 | hc3
        · rcases Nat.lt_or_ge n 699268608 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert102 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 705351204 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert103 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert104 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 717526298 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert105 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 723611424 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert106 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert107 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 748005188 with hc9 | hc9
        · rcases Nat.lt_or_ge n 735806570 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert108 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 741897012 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert109 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert110 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 754116218 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert111 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 760217454 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert112 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert113 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 803009258 with hc18 | hc18
      · rcases Nat.lt_or_ge n 784659612 with hc15 | hc15
        · rcases Nat.lt_or_ge n 772433478 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert114 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 778549394 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert115 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert116 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 790765920 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert117 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 796888034 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert118 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert119 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 821378672 with hc21 | hc21
        · rcases Nat.lt_or_ge n 809125862 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert120 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 815255994 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert121 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert122 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 833642058 with hc23 | hc23
          · rcases Nat.lt_or_ge n 827510988 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert123 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert124 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 839774562 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert125 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert126 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 919722338 with hc37 | hc37
    · rcases Nat.lt_or_ge n 882785598 with hc31 | hc31
      · rcases Nat.lt_or_ge n 864342252 with hc28 | hc28
        · rcases Nat.lt_or_ge n 852054188 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert127 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 858192092 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert128 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert129 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 870482720 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert130 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 876634988 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert131 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert132 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 901255308 with hc34 | hc34
        · rcases Nat.lt_or_ge n 888940590 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert133 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 895099244 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert134 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert135 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 907413294 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert136 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 913563882 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert137 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert138 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 956743928 with hc43 | hc43
      · rcases Nat.lt_or_ge n 938225552 with hc40 | hc40
        · rcases Nat.lt_or_ge n 925885824 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert139 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 932059862 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert140 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert141 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 944397662 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert142 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 950571314 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert143 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert144 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 975269910 with hc46 | hc46
        · rcases Nat.lt_or_ge n 962909808 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert145 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 969088578 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert146 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert147 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 987633810 with hc48 | hc48
          · rcases Nat.lt_or_ge n 981454742 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert148 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert149 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 993817664 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert150 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert151 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real))
    (n : Nat) (h1 : 693190904 <= n) (h2 : n <= 1000000000) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real)) :=
  TFPLink.blk hbase n h1 h2
