-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp24
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T03:56:39.538077+00:00
-- url     : https://prove2.me/submissions/e57d3271-c759-4f90-b661-fbd2549e182c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1151
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1152
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1153
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1154
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1155
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1156
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1157
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1158
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1159
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1160
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1161
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1162
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1163
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1164
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1165
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1166
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1167
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1168
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1169
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1170
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1171
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1172
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1173
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1174
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1175
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1176
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1177
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1178
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1179
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1180
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1181
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1182
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1183
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1184
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1185
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1186
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1187
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1188
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1189
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1190
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1191
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1192
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1193
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1194
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1195
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1196
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1197
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1198
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1199
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1200

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp24` (the range 8637206844 <= n <= 8980547699 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1151` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1200`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (9496615449774559403785 : Real) / 2 ^ 40 <= Chebyshev.theta (8637206844 : Real))
    (n : Nat) (h1 : 8637206844 <= n) (h2 : n <= 8980547699) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9874099226388381058938 : Real) / 2 ^ 40 <= Chebyshev.theta (8980547700 : Real)) := by
  have hb0 := hbase
  have hb1 : (9504158789909468456232 : Real) / 2 ^ 40 <= Chebyshev.theta (8644064168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1151 hb0 8637206844 le_rfl (by norm_num)).2
  have hb2 : (9511702391656253807863 : Real) / 2 ^ 40 <= Chebyshev.theta (8650927992 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1152 hb1 8644064168 le_rfl (by norm_num)).2
  have hb3 : (9519246255048407208972 : Real) / 2 ^ 40 <= Chebyshev.theta (8657787420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1153 hb2 8650927992 le_rfl (by norm_num)).2
  have hb4 : (9526790379876047024376 : Real) / 2 ^ 40 <= Chebyshev.theta (8664658394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1154 hb3 8657787420 le_rfl (by norm_num)).2
  have hb5 : (9534334766096936435646 : Real) / 2 ^ 40 <= Chebyshev.theta (8671526778 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1155 hb4 8664658394 le_rfl (by norm_num)).2
  have hb6 : (9541879413251680267897 : Real) / 2 ^ 40 <= Chebyshev.theta (8678383740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1156 hb5 8671526778 le_rfl (by norm_num)).2
  have hb7 : (9549424321237198356331 : Real) / 2 ^ 40 <= Chebyshev.theta (8685260798 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1157 hb6 8678383740 le_rfl (by norm_num)).2
  have hb8 : (9556969489882310643882 : Real) / 2 ^ 40 <= Chebyshev.theta (8692117844 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1158 hb7 8685260798 le_rfl (by norm_num)).2
  have hb9 : (9564514918567047619526 : Real) / 2 ^ 40 <= Chebyshev.theta (8698975758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1159 hb8 8692117844 le_rfl (by norm_num)).2
  have hb10 : (9572060607123206270669 : Real) / 2 ^ 40 <= Chebyshev.theta (8705832254 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1160 hb9 8698975758 le_rfl (by norm_num)).2
  have hb11 : (9579606555563811166870 : Real) / 2 ^ 40 <= Chebyshev.theta (8712700310 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1161 hb10 8705832254 le_rfl (by norm_num)).2
  have hb12 : (9587152763714147010755 : Real) / 2 ^ 40 <= Chebyshev.theta (8719553334 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1162 hb11 8712700310 le_rfl (by norm_num)).2
  have hb13 : (9594699231210642246339 : Real) / 2 ^ 40 <= Chebyshev.theta (8726419410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1163 hb12 8719553334 le_rfl (by norm_num)).2
  have hb14 : (9602245958137770510478 : Real) / 2 ^ 40 <= Chebyshev.theta (8733287360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1164 hb13 8726419410 le_rfl (by norm_num)).2
  have hb15 : (9609792944067023464670 : Real) / 2 ^ 40 <= Chebyshev.theta (8740145642 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1165 hb14 8733287360 le_rfl (by norm_num)).2
  have hb16 : (9617340188958583139120 : Real) / 2 ^ 40 <= Chebyshev.theta (8747019714 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1166 hb15 8740145642 le_rfl (by norm_num)).2
  have hb17 : (9624887693042054088631 : Real) / 2 ^ 40 <= Chebyshev.theta (8753888024 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1167 hb16 8747019714 le_rfl (by norm_num)).2
  have hb18 : (9632435455706397935590 : Real) / 2 ^ 40 <= Chebyshev.theta (8760758558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1168 hb17 8753888024 le_rfl (by norm_num)).2
  have hb19 : (9639983476985478560853 : Real) / 2 ^ 40 <= Chebyshev.theta (8767625960 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1169 hb18 8760758558 le_rfl (by norm_num)).2
  have hb20 : (9647531756389572148988 : Real) / 2 ^ 40 <= Chebyshev.theta (8774492172 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1170 hb19 8767625960 le_rfl (by norm_num)).2
  have hb21 : (9655080294001291684058 : Real) / 2 ^ 40 <= Chebyshev.theta (8781358058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1171 hb20 8774492172 le_rfl (by norm_num)).2
  have hb22 : (9662629089070980155283 : Real) / 2 ^ 40 <= Chebyshev.theta (8788216850 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1172 hb21 8781358058 le_rfl (by norm_num)).2
  have hb23 : (9670178141619476873959 : Real) / 2 ^ 40 <= Chebyshev.theta (8795083860 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1173 hb22 8788216850 le_rfl (by norm_num)).2
  have hb24 : (9677727451473368999667 : Real) / 2 ^ 40 <= Chebyshev.theta (8801946500 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1174 hb23 8795083860 le_rfl (by norm_num)).2
  have hb25 : (9685277018472640392106 : Real) / 2 ^ 40 <= Chebyshev.theta (8808814398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1175 hb24 8801946500 le_rfl (by norm_num)).2
  have hb26 : (9692826842476811765316 : Real) / 2 ^ 40 <= Chebyshev.theta (8815681794 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1176 hb25 8808814398 le_rfl (by norm_num)).2
  have hb27 : (9700376923346520225011 : Real) / 2 ^ 40 <= Chebyshev.theta (8822547554 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1177 hb26 8815681794 le_rfl (by norm_num)).2
  have hb28 : (9707927260864627590110 : Real) / 2 ^ 40 <= Chebyshev.theta (8829409298 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1178 hb27 8822547554 le_rfl (by norm_num)).2
  have hb29 : (9715477854636117272406 : Real) / 2 ^ 40 <= Chebyshev.theta (8836278822 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1179 hb28 8829409298 le_rfl (by norm_num)).2
  have hb30 : (9723028704636986850855 : Real) / 2 ^ 40 <= Chebyshev.theta (8843141534 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1180 hb29 8836278822 le_rfl (by norm_num)).2
  have hb31 : (9730579810445984532851 : Real) / 2 ^ 40 <= Chebyshev.theta (8850005348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1181 hb30 8843141534 le_rfl (by norm_num)).2
  have hb32 : (9738131172018268586055 : Real) / 2 ^ 40 <= Chebyshev.theta (8856873822 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1182 hb31 8850005348 le_rfl (by norm_num)).2
  have hb33 : (9745682789362770143879 : Real) / 2 ^ 40 <= Chebyshev.theta (8863749332 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1183 hb32 8856873822 le_rfl (by norm_num)).2
  have hb34 : (9753234662342545160671 : Real) / 2 ^ 40 <= Chebyshev.theta (8870613608 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1184 hb33 8863749332 le_rfl (by norm_num)).2
  have hb35 : (9760786790527224645134 : Real) / 2 ^ 40 <= Chebyshev.theta (8877483048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1185 hb34 8870613608 le_rfl (by norm_num)).2
  have hb36 : (9768339173850941488354 : Real) / 2 ^ 40 <= Chebyshev.theta (8884351188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1186 hb35 8877483048 le_rfl (by norm_num)).2
  have hb37 : (9775891812208196676901 : Real) / 2 ^ 40 <= Chebyshev.theta (8891225730 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1187 hb36 8884351188 le_rfl (by norm_num)).2
  have hb38 : (9783444705295703805322 : Real) / 2 ^ 40 <= Chebyshev.theta (8898096972 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1188 hb37 8891225730 le_rfl (by norm_num)).2
  have hb39 : (9790997853033454803467 : Real) / 2 ^ 40 <= Chebyshev.theta (8904974510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1189 hb38 8898096972 le_rfl (by norm_num)).2
  have hb40 : (9798551255311671156478 : Real) / 2 ^ 40 <= Chebyshev.theta (8911847768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1190 hb39 8904974510 le_rfl (by norm_num)).2
  have hb41 : (9806104911949869543319 : Real) / 2 ^ 40 <= Chebyshev.theta (8918717922 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1191 hb40 8911847768 le_rfl (by norm_num)).2
  have hb42 : (9813658822639553730714 : Real) / 2 ^ 40 <= Chebyshev.theta (8925592044 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1192 hb41 8918717922 le_rfl (by norm_num)).2
  have hb43 : (9821212986891185968511 : Real) / 2 ^ 40 <= Chebyshev.theta (8932451940 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1193 hb42 8925592044 le_rfl (by norm_num)).2
  have hb44 : (9828767404598895112721 : Real) / 2 ^ 40 <= Chebyshev.theta (8939323664 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1194 hb43 8932451940 le_rfl (by norm_num)).2
  have hb45 : (9836322075773100818991 : Real) / 2 ^ 40 <= Chebyshev.theta (8946193304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1195 hb44 8939323664 le_rfl (by norm_num)).2
  have hb46 : (9843877000141217452973 : Real) / 2 ^ 40 <= Chebyshev.theta (8953069164 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1196 hb45 8946193304 le_rfl (by norm_num)).2
  have hb47 : (9851432177457080649995 : Real) / 2 ^ 40 <= Chebyshev.theta (8959932572 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1197 hb46 8953069164 le_rfl (by norm_num)).2
  have hb48 : (9858987607767206729912 : Real) / 2 ^ 40 <= Chebyshev.theta (8966814072 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1198 hb47 8959932572 le_rfl (by norm_num)).2
  have hb49 : (9866543290926092644219 : Real) / 2 ^ 40 <= Chebyshev.theta (8973688320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1199 hb48 8966814072 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1200 hb49 8973688320 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 8808814398 with hc25 | hc25
  · rcases Nat.lt_or_ge n 8719553334 with hc12 | hc12
    · rcases Nat.lt_or_ge n 8678383740 with hc6 | hc6
      · rcases Nat.lt_or_ge n 8657787420 with hc3 | hc3
        · rcases Nat.lt_or_ge n 8644064168 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1151 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8650927992 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1152 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1153 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8664658394 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1154 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8671526778 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1155 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1156 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8698975758 with hc9 | hc9
        · rcases Nat.lt_or_ge n 8685260798 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1157 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8692117844 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1158 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1159 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8705832254 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1160 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8712700310 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1161 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1162 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8760758558 with hc18 | hc18
      · rcases Nat.lt_or_ge n 8740145642 with hc15 | hc15
        · rcases Nat.lt_or_ge n 8726419410 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1163 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8733287360 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1164 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1165 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8747019714 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1166 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8753888024 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1167 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1168 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8781358058 with hc21 | hc21
        · rcases Nat.lt_or_ge n 8767625960 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1169 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8774492172 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1170 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1171 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8795083860 with hc23 | hc23
          · rcases Nat.lt_or_ge n 8788216850 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1172 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1173 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8801946500 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1174 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1175 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 8891225730 with hc37 | hc37
    · rcases Nat.lt_or_ge n 8850005348 with hc31 | hc31
      · rcases Nat.lt_or_ge n 8829409298 with hc28 | hc28
        · rcases Nat.lt_or_ge n 8815681794 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1176 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8822547554 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1177 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1178 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8836278822 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1179 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8843141534 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1180 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1181 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8870613608 with hc34 | hc34
        · rcases Nat.lt_or_ge n 8856873822 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1182 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8863749332 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1183 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1184 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8877483048 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1185 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8884351188 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1186 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1187 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8932451940 with hc43 | hc43
      · rcases Nat.lt_or_ge n 8911847768 with hc40 | hc40
        · rcases Nat.lt_or_ge n 8898096972 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1188 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8904974510 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1189 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1190 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8918717922 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1191 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8925592044 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1192 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1193 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8953069164 with hc46 | hc46
        · rcases Nat.lt_or_ge n 8939323664 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1194 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8946193304 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1195 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1196 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8966814072 with hc48 | hc48
          · rcases Nat.lt_or_ge n 8959932572 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1197 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1198 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8973688320 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1199 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1200 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (9496615449774559403785 : Real) / 2 ^ 40 <= Chebyshev.theta (8637206844 : Real))
    (n : Nat) (h1 : 8637206844 <= n) (h2 : n <= 8980547699) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9874099226388381058938 : Real) / 2 ^ 40 <= Chebyshev.theta (8980547700 : Real)) :=
  TFPLink.blk hbase n h1 h2
