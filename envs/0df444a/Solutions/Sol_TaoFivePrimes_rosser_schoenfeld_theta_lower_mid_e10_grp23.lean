-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp23
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T02:54:18.723598+00:00
-- url     : https://prove2.me/submissions/adc492d7-6752-4b82-8ee1-84466a25abc9

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1101
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1102
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1103
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1104
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1105
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1106
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1107
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1108
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1109
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1110
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1111
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1112
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1113
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1114
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1115
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1116
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1117
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1118
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1119
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1120
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1121
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1122
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1123
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1124
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1125
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1126
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1127
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1128
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1129
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1130
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1131
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1132
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1133
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1134
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1135
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1136
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1137
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1138
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1139
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1140
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1141
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1142
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1143
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1144
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1145
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1146
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1147
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1148
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1149
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1150

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp23` (the range 8294482074 <= n <= 8637206843 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1101` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1150`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (9119786553842252571751 : Real) / 2 ^ 40 <= Chebyshev.theta (8294482074 : Real))
    (n : Nat) (h1 : 8294482074 <= n) (h2 : n <= 8637206843) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9496615449774559403785 : Real) / 2 ^ 40 <= Chebyshev.theta (8637206844 : Real)) := by
  have hb0 := hbase
  have hb1 : (9127316550233640831443 : Real) / 2 ^ 40 <= Chebyshev.theta (8301326718 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1101 hb0 8294482074 le_rfl (by norm_num)).2
  have hb2 : (9134846818335040234943 : Real) / 2 ^ 40 <= Chebyshev.theta (8308172648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1102 hb1 8301326718 le_rfl (by norm_num)).2
  have hb3 : (9142377358245065380343 : Real) / 2 ^ 40 <= Chebyshev.theta (8315026482 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1103 hb2 8308172648 le_rfl (by norm_num)).2
  have hb4 : (9149908170156293831843 : Real) / 2 ^ 40 <= Chebyshev.theta (8321884340 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1104 hb3 8315026482 le_rfl (by norm_num)).2
  have hb5 : (9157439253523182190185 : Real) / 2 ^ 40 <= Chebyshev.theta (8328731684 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1105 hb4 8321884340 le_rfl (by norm_num)).2
  have hb6 : (9164970608210460997233 : Real) / 2 ^ 40 <= Chebyshev.theta (8335585542 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1106 hb5 8328731684 le_rfl (by norm_num)).2
  have hb7 : (9172502233612859899036 : Real) / 2 ^ 40 <= Chebyshev.theta (8342427422 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1107 hb6 8335585542 le_rfl (by norm_num)).2
  have hb8 : (9180034129600877461119 : Real) / 2 ^ 40 <= Chebyshev.theta (8349276620 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1108 hb7 8342427422 le_rfl (by norm_num)).2
  have hb9 : (9187566296129299820583 : Real) / 2 ^ 40 <= Chebyshev.theta (8356128788 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1109 hb8 8349276620 le_rfl (by norm_num)).2
  have hb10 : (9195098732895956963651 : Real) / 2 ^ 40 <= Chebyshev.theta (8362976340 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1110 hb9 8356128788 le_rfl (by norm_num)).2
  have hb11 : (9202631439387680849686 : Real) / 2 ^ 40 <= Chebyshev.theta (8369814312 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1111 hb10 8362976340 le_rfl (by norm_num)).2
  have hb12 : (9210164415667919738970 : Real) / 2 ^ 40 <= Chebyshev.theta (8376672920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1112 hb11 8369814312 le_rfl (by norm_num)).2
  have hb13 : (9217697661785794865270 : Real) / 2 ^ 40 <= Chebyshev.theta (8383527108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1113 hb12 8376672920 le_rfl (by norm_num)).2
  have hb14 : (9225231177471697638708 : Real) / 2 ^ 40 <= Chebyshev.theta (8390379374 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1114 hb13 8383527108 le_rfl (by norm_num)).2
  have hb15 : (9232764962633339680691 : Real) / 2 ^ 40 <= Chebyshev.theta (8397239990 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1115 hb14 8390379374 le_rfl (by norm_num)).2
  have hb16 : (9240299016688150601359 : Real) / 2 ^ 40 <= Chebyshev.theta (8404085084 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1116 hb15 8397239990 le_rfl (by norm_num)).2
  have hb17 : (9247833339504210117604 : Real) / 2 ^ 40 <= Chebyshev.theta (8410939280 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1117 hb16 8404085084 le_rfl (by norm_num)).2
  have hb18 : (9255367930962622515878 : Real) / 2 ^ 40 <= Chebyshev.theta (8417791178 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1118 hb17 8410939280 le_rfl (by norm_num)).2
  have hb19 : (9262902790851645508201 : Real) / 2 ^ 40 <= Chebyshev.theta (8424637704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1119 hb18 8417791178 le_rfl (by norm_num)).2
  have hb20 : (9270437918727885533719 : Real) / 2 ^ 40 <= Chebyshev.theta (8431495562 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1120 hb19 8424637704 le_rfl (by norm_num)).2
  have hb21 : (9277973314460724766279 : Real) / 2 ^ 40 <= Chebyshev.theta (8438340452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1121 hb20 8431495562 le_rfl (by norm_num)).2
  have hb22 : (9285508978081236107544 : Real) / 2 ^ 40 <= Chebyshev.theta (8445209892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1122 hb21 8438340452 le_rfl (by norm_num)).2
  have hb23 : (9293044909640773574633 : Real) / 2 ^ 40 <= Chebyshev.theta (8452072748 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1123 hb22 8445209892 le_rfl (by norm_num)).2
  have hb24 : (9300581108818374560549 : Real) / 2 ^ 40 <= Chebyshev.theta (8458928268 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1124 hb23 8452072748 le_rfl (by norm_num)).2
  have hb25 : (9308117575122082466509 : Real) / 2 ^ 40 <= Chebyshev.theta (8465765198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1125 hb24 8458928268 le_rfl (by norm_num)).2
  have hb26 : (9315654308234655991103 : Real) / 2 ^ 40 <= Chebyshev.theta (8472636830 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1126 hb25 8465765198 le_rfl (by norm_num)).2
  have hb27 : (9323191308532691259875 : Real) / 2 ^ 40 <= Chebyshev.theta (8479497294 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1127 hb26 8472636830 le_rfl (by norm_num)).2
  have hb28 : (9330728575209223155985 : Real) / 2 ^ 40 <= Chebyshev.theta (8486344418 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1128 hb27 8479497294 le_rfl (by norm_num)).2
  have hb29 : (9338266108077070008337 : Real) / 2 ^ 40 <= Chebyshev.theta (8493197304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1129 hb28 8486344418 le_rfl (by norm_num)).2
  have hb30 : (9345803907081900755342 : Real) / 2 ^ 40 <= Chebyshev.theta (8500054712 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1130 hb29 8493197304 le_rfl (by norm_num)).2
  have hb31 : (9353341971899403614972 : Real) / 2 ^ 40 <= Chebyshev.theta (8506907420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1131 hb30 8500054712 le_rfl (by norm_num)).2
  have hb32 : (9360880302487527834078 : Real) / 2 ^ 40 <= Chebyshev.theta (8513766092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1132 hb31 8506907420 le_rfl (by norm_num)).2
  have hb33 : (9368418898570152538003 : Real) / 2 ^ 40 <= Chebyshev.theta (8520620822 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1133 hb32 8513766092 le_rfl (by norm_num)).2
  have hb34 : (9375957759764541446981 : Real) / 2 ^ 40 <= Chebyshev.theta (8527474370 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1134 hb33 8520620822 le_rfl (by norm_num)).2
  have hb35 : (9383496886269784409991 : Real) / 2 ^ 40 <= Chebyshev.theta (8534337090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1135 hb34 8527474370 le_rfl (by norm_num)).2
  have hb36 : (9391036277610670703398 : Real) / 2 ^ 40 <= Chebyshev.theta (8541191654 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1136 hb35 8534337090 le_rfl (by norm_num)).2
  have hb37 : (9398575933551083487618 : Real) / 2 ^ 40 <= Chebyshev.theta (8548045698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1137 hb36 8541191654 le_rfl (by norm_num)).2
  have hb38 : (9406115853711263527357 : Real) / 2 ^ 40 <= Chebyshev.theta (8554887968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1138 hb37 8548045698 le_rfl (by norm_num)).2
  have hb39 : (9413656037923007810021 : Real) / 2 ^ 40 <= Chebyshev.theta (8561748698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1139 hb38 8554887968 le_rfl (by norm_num)).2
  have hb40 : (9421196486113192680798 : Real) / 2 ^ 40 <= Chebyshev.theta (8568599402 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1140 hb39 8561748698 le_rfl (by norm_num)).2
  have hb41 : (9428737198065982415562 : Real) / 2 ^ 40 <= Chebyshev.theta (8575462280 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1141 hb40 8568599402 le_rfl (by norm_num)).2
  have hb42 : (9436278174046706102765 : Real) / 2 ^ 40 <= Chebyshev.theta (8582331672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1142 hb41 8575462280 le_rfl (by norm_num)).2
  have hb43 : (9443819413694955296172 : Real) / 2 ^ 40 <= Chebyshev.theta (8589185024 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1143 hb42 8582331672 le_rfl (by norm_num)).2
  have hb44 : (9451360916282284426858 : Real) / 2 ^ 40 <= Chebyshev.theta (8596037294 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1144 hb43 8589185024 le_rfl (by norm_num)).2
  have hb45 : (9458902681886654846899 : Real) / 2 ^ 40 <= Chebyshev.theta (8602900128 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1145 hb44 8596037294 le_rfl (by norm_num)).2
  have hb46 : (9466444710271949716713 : Real) / 2 ^ 40 <= Chebyshev.theta (8609752722 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1146 hb45 8602900128 le_rfl (by norm_num)).2
  have hb47 : (9473987001514083670302 : Real) / 2 ^ 40 <= Chebyshev.theta (8616623624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1147 hb46 8609752722 le_rfl (by norm_num)).2
  have hb48 : (9481529555379730847276 : Real) / 2 ^ 40 <= Chebyshev.theta (8623483434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1148 hb47 8616623624 le_rfl (by norm_num)).2
  have hb49 : (9489072371569140082490 : Real) / 2 ^ 40 <= Chebyshev.theta (8630345768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1149 hb48 8623483434 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1150 hb49 8630345768 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 8465765198 with hc25 | hc25
  · rcases Nat.lt_or_ge n 8376672920 with hc12 | hc12
    · rcases Nat.lt_or_ge n 8335585542 with hc6 | hc6
      · rcases Nat.lt_or_ge n 8315026482 with hc3 | hc3
        · rcases Nat.lt_or_ge n 8301326718 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1101 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8308172648 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1102 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1103 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8321884340 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1104 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8328731684 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1105 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1106 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8356128788 with hc9 | hc9
        · rcases Nat.lt_or_ge n 8342427422 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1107 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8349276620 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1108 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1109 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8362976340 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1110 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8369814312 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1111 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1112 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8417791178 with hc18 | hc18
      · rcases Nat.lt_or_ge n 8397239990 with hc15 | hc15
        · rcases Nat.lt_or_ge n 8383527108 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1113 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8390379374 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1114 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1115 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8404085084 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1116 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8410939280 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1117 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1118 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8438340452 with hc21 | hc21
        · rcases Nat.lt_or_ge n 8424637704 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1119 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8431495562 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1120 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1121 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8452072748 with hc23 | hc23
          · rcases Nat.lt_or_ge n 8445209892 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1122 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1123 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8458928268 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1124 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1125 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 8548045698 with hc37 | hc37
    · rcases Nat.lt_or_ge n 8506907420 with hc31 | hc31
      · rcases Nat.lt_or_ge n 8486344418 with hc28 | hc28
        · rcases Nat.lt_or_ge n 8472636830 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1126 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8479497294 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1127 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1128 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8493197304 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1129 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8500054712 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1130 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1131 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8527474370 with hc34 | hc34
        · rcases Nat.lt_or_ge n 8513766092 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1132 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8520620822 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1133 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1134 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8534337090 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1135 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8541191654 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1136 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1137 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8589185024 with hc43 | hc43
      · rcases Nat.lt_or_ge n 8568599402 with hc40 | hc40
        · rcases Nat.lt_or_ge n 8554887968 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1138 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8561748698 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1139 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1140 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8575462280 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1141 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8582331672 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1142 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1143 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8609752722 with hc46 | hc46
        · rcases Nat.lt_or_ge n 8596037294 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1144 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8602900128 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1145 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1146 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8623483434 with hc48 | hc48
          · rcases Nat.lt_or_ge n 8616623624 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1147 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1148 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8630345768 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1149 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1150 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (9119786553842252571751 : Real) / 2 ^ 40 <= Chebyshev.theta (8294482074 : Real))
    (n : Nat) (h1 : 8294482074 <= n) (h2 : n <= 8637206843) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9496615449774559403785 : Real) / 2 ^ 40 <= Chebyshev.theta (8637206844 : Real)) :=
  TFPLink.blk hbase n h1 h2
