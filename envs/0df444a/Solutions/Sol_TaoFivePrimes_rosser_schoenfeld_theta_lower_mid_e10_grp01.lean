-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:39:49.282093+00:00
-- url     : https://prove2.me/submissions/961c84cc-233c-48f2-a0fd-9978f761c6a6

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0001
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0002
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0003
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0004
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0005
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0006
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0007
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0008
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0009
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0010
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0011
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0012
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0013
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0014
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0015
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0016
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0017
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0018
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0019
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0020
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0021
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0022
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0023
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0024
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0025
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0026
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0027
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0028
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0029
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0030
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0031
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0032
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0033
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0034
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0035
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0036
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0037
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0038
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0039
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0040
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0041
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0042
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0043
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0044
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0045
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0046
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0047
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0048
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0049
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0050

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01` (the range 1000000001 <= n <= 1312834711 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0001` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0050`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real))
    (n : Nat) (h1 : 1000000001 <= n) (h2 : n <= 1312834711) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real)) := by
  have hb0 := hbase
  have hb1 : (1106302403100715334309 : Real) / 2 ^ 40 <= Chebyshev.theta (1006214802 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0001 hb0 1000000001 le_rfl (by norm_num)).2
  have hb2 : (1113137822547394841600 : Real) / 2 ^ 40 <= Chebyshev.theta (1012430214 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0002 hb1 1006214802 le_rfl (by norm_num)).2
  have hb3 : (1119975265848446422283 : Real) / 2 ^ 40 <= Chebyshev.theta (1018645074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0003 hb2 1012430214 le_rfl (by norm_num)).2
  have hb4 : (1126814721841813964015 : Real) / 2 ^ 40 <= Chebyshev.theta (1024866374 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0004 hb3 1018645074 le_rfl (by norm_num)).2
  have hb5 : (1133656179230916157434 : Real) / 2 ^ 40 <= Chebyshev.theta (1031087882 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0005 hb4 1024866374 le_rfl (by norm_num)).2
  have hb6 : (1140499627073626050471 : Real) / 2 ^ 40 <= Chebyshev.theta (1037315970 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0006 hb5 1031087882 le_rfl (by norm_num)).2
  have hb7 : (1147345052349095389388 : Real) / 2 ^ 40 <= Chebyshev.theta (1043534088 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0007 hb6 1037315970 le_rfl (by norm_num)).2
  have hb8 : (1154192445293362571397 : Real) / 2 ^ 40 <= Chebyshev.theta (1049771202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0008 hb7 1043534088 le_rfl (by norm_num)).2
  have hb9 : (1161041795823550104785 : Real) / 2 ^ 40 <= Chebyshev.theta (1056003548 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0009 hb8 1049771202 le_rfl (by norm_num)).2
  have hb10 : (1167893092889427110140 : Real) / 2 ^ 40 <= Chebyshev.theta (1062236810 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0010 hb9 1056003548 le_rfl (by norm_num)).2
  have hb11 : (1174746323585505806964 : Real) / 2 ^ 40 <= Chebyshev.theta (1068462350 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0011 hb10 1062236810 le_rfl (by norm_num)).2
  have hb12 : (1181601475443737886673 : Real) / 2 ^ 40 <= Chebyshev.theta (1074692604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0012 hb11 1068462350 le_rfl (by norm_num)).2
  have hb13 : (1188458541810987153084 : Real) / 2 ^ 40 <= Chebyshev.theta (1080937424 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0013 hb12 1074692604 le_rfl (by norm_num)).2
  have hb14 : (1195317509273249417047 : Real) / 2 ^ 40 <= Chebyshev.theta (1087164320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0014 hb13 1080937424 le_rfl (by norm_num)).2
  have hb15 : (1202178367453105849529 : Real) / 2 ^ 40 <= Chebyshev.theta (1093400774 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0015 hb14 1087164320 le_rfl (by norm_num)).2
  have hb16 : (1209041106589199761653 : Real) / 2 ^ 40 <= Chebyshev.theta (1099642208 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0016 hb15 1093400774 le_rfl (by norm_num)).2
  have hb17 : (1215905717160756870832 : Real) / 2 ^ 40 <= Chebyshev.theta (1105885328 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0017 hb16 1099642208 le_rfl (by norm_num)).2
  have hb18 : (1222772188533402197155 : Real) / 2 ^ 40 <= Chebyshev.theta (1112127224 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0018 hb17 1105885328 le_rfl (by norm_num)).2
  have hb19 : (1229640512112966549540 : Real) / 2 ^ 40 <= Chebyshev.theta (1118378760 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0019 hb18 1112127224 le_rfl (by norm_num)).2
  have hb20 : (1236510677537288451867 : Real) / 2 ^ 40 <= Chebyshev.theta (1124629370 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0020 hb19 1118378760 le_rfl (by norm_num)).2
  have hb21 : (1243382676301137916617 : Real) / 2 ^ 40 <= Chebyshev.theta (1130882610 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0021 hb20 1124629370 le_rfl (by norm_num)).2
  have hb22 : (1250256499338856334660 : Real) / 2 ^ 40 <= Chebyshev.theta (1137147482 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0022 hb21 1130882610 le_rfl (by norm_num)).2
  have hb23 : (1257132137441514831715 : Real) / 2 ^ 40 <= Chebyshev.theta (1143406992 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0023 hb22 1137147482 le_rfl (by norm_num)).2
  have hb24 : (1264009581411720580823 : Real) / 2 ^ 40 <= Chebyshev.theta (1149661062 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0024 hb23 1143406992 le_rfl (by norm_num)).2
  have hb25 : (1270888817930548750618 : Real) / 2 ^ 40 <= Chebyshev.theta (1155913154 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0025 hb24 1149661062 le_rfl (by norm_num)).2
  have hb26 : (1277769838480302979859 : Real) / 2 ^ 40 <= Chebyshev.theta (1162168692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0026 hb25 1155913154 le_rfl (by norm_num)).2
  have hb27 : (1284652633532580309502 : Real) / 2 ^ 40 <= Chebyshev.theta (1168425852 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0027 hb26 1162168692 le_rfl (by norm_num)).2
  have hb28 : (1291537194724676756063 : Real) / 2 ^ 40 <= Chebyshev.theta (1174682990 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0028 hb27 1168425852 le_rfl (by norm_num)).2
  have hb29 : (1298423513043962315047 : Real) / 2 ^ 40 <= Chebyshev.theta (1180950062 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0029 hb28 1174682990 le_rfl (by norm_num)).2
  have hb30 : (1305311582273437805229 : Real) / 2 ^ 40 <= Chebyshev.theta (1187224154 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0030 hb29 1180950062 le_rfl (by norm_num)).2
  have hb31 : (1312201391879017432305 : Real) / 2 ^ 40 <= Chebyshev.theta (1193486462 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0031 hb30 1187224154 le_rfl (by norm_num)).2
  have hb32 : (1319092932933661220313 : Real) / 2 ^ 40 <= Chebyshev.theta (1199753924 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0032 hb31 1193486462 le_rfl (by norm_num)).2
  have hb33 : (1325986197582809463861 : Real) / 2 ^ 40 <= Chebyshev.theta (1206030740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0033 hb32 1199753924 le_rfl (by norm_num)).2
  have hb34 : (1332881176172837270857 : Real) / 2 ^ 40 <= Chebyshev.theta (1212297158 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0034 hb33 1206030740 le_rfl (by norm_num)).2
  have hb35 : (1339777859983609256052 : Real) / 2 ^ 40 <= Chebyshev.theta (1218570258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0035 hb34 1212297158 le_rfl (by norm_num)).2
  have hb36 : (1346676240446633236925 : Real) / 2 ^ 40 <= Chebyshev.theta (1224841638 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0036 hb35 1218570258 le_rfl (by norm_num)).2
  have hb37 : (1353576312069448230307 : Real) / 2 ^ 40 <= Chebyshev.theta (1231123040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0037 hb36 1224841638 le_rfl (by norm_num)).2
  have hb38 : (1360478064451935443077 : Real) / 2 ^ 40 <= Chebyshev.theta (1237401224 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0038 hb37 1231123040 le_rfl (by norm_num)).2
  have hb39 : (1367381490360993203102 : Real) / 2 ^ 40 <= Chebyshev.theta (1243688904 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0039 hb38 1237401224 le_rfl (by norm_num)).2
  have hb40 : (1374286581162262218947 : Real) / 2 ^ 40 <= Chebyshev.theta (1249960850 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0040 hb39 1243688904 le_rfl (by norm_num)).2
  have hb41 : (1381193326768771562752 : Real) / 2 ^ 40 <= Chebyshev.theta (1256242778 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0041 hb40 1249960850 le_rfl (by norm_num)).2
  have hb42 : (1388101722009581054184 : Real) / 2 ^ 40 <= Chebyshev.theta (1262525322 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0042 hb41 1256242778 le_rfl (by norm_num)).2
  have hb43 : (1395011757790191965805 : Real) / 2 ^ 40 <= Chebyshev.theta (1268803560 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0043 hb42 1262525322 le_rfl (by norm_num)).2
  have hb44 : (1401923424889395114891 : Real) / 2 ^ 40 <= Chebyshev.theta (1275089144 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0044 hb43 1268803560 le_rfl (by norm_num)).2
  have hb45 : (1408836718017726738120 : Real) / 2 ^ 40 <= Chebyshev.theta (1281377088 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0045 hb44 1275089144 le_rfl (by norm_num)).2
  have hb46 : (1415751629381470476471 : Real) / 2 ^ 40 <= Chebyshev.theta (1287665958 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0046 hb45 1281377088 le_rfl (by norm_num)).2
  have hb47 : (1422668150882135043235 : Real) / 2 ^ 40 <= Chebyshev.theta (1293956102 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0047 hb46 1287665958 le_rfl (by norm_num)).2
  have hb48 : (1429586276923807159887 : Real) / 2 ^ 40 <= Chebyshev.theta (1300256624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0048 hb47 1293956102 le_rfl (by norm_num)).2
  have hb49 : (1436505998865801315490 : Real) / 2 ^ 40 <= Chebyshev.theta (1306545960 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0049 hb48 1300256624 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0050 hb49 1306545960 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 1155913154 with hc25 | hc25
  · rcases Nat.lt_or_ge n 1074692604 with hc12 | hc12
    · rcases Nat.lt_or_ge n 1037315970 with hc6 | hc6
      · rcases Nat.lt_or_ge n 1018645074 with hc3 | hc3
        · rcases Nat.lt_or_ge n 1006214802 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0001 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1012430214 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0002 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0003 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1024866374 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0004 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1031087882 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0005 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0006 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1056003548 with hc9 | hc9
        · rcases Nat.lt_or_ge n 1043534088 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0007 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1049771202 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0008 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0009 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1062236810 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0010 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1068462350 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0011 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0012 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1112127224 with hc18 | hc18
      · rcases Nat.lt_or_ge n 1093400774 with hc15 | hc15
        · rcases Nat.lt_or_ge n 1080937424 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0013 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1087164320 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0014 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0015 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1099642208 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0016 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1105885328 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0017 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0018 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1130882610 with hc21 | hc21
        · rcases Nat.lt_or_ge n 1118378760 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0019 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1124629370 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0020 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0021 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1143406992 with hc23 | hc23
          · rcases Nat.lt_or_ge n 1137147482 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0022 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0023 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1149661062 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0024 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0025 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 1231123040 with hc37 | hc37
    · rcases Nat.lt_or_ge n 1193486462 with hc31 | hc31
      · rcases Nat.lt_or_ge n 1174682990 with hc28 | hc28
        · rcases Nat.lt_or_ge n 1162168692 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0026 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1168425852 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0027 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0028 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1180950062 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0029 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1187224154 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0030 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0031 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1212297158 with hc34 | hc34
        · rcases Nat.lt_or_ge n 1199753924 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0032 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1206030740 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0033 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0034 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1218570258 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0035 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1224841638 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0036 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0037 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1268803560 with hc43 | hc43
      · rcases Nat.lt_or_ge n 1249960850 with hc40 | hc40
        · rcases Nat.lt_or_ge n 1237401224 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0038 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1243688904 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0039 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0040 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1256242778 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0041 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1262525322 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0042 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0043 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1287665958 with hc46 | hc46
        · rcases Nat.lt_or_ge n 1275089144 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0044 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1281377088 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0045 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0046 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1300256624 with hc48 | hc48
          · rcases Nat.lt_or_ge n 1293956102 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0047 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0048 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1306545960 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0049 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0050 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real))
    (n : Nat) (h1 : 1000000001 <= n) (h2 : n <= 1312834711) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real)) :=
  TFPLink.blk hbase n h1 h2
