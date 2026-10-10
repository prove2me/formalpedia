-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp02
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:50:08.35865+00:00
-- url     : https://prove2.me/submissions/c1456b9c-b18e-40dc-a464-6628fac87aab

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0051
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0052
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0053
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0054
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0055
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0056
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0057
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0058
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0059
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0060
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0061
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0062
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0063
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0064
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0065
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0066
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0067
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0068
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0069
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0070
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0071
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0072
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0073
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0074
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0075
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0076
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0077
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0078
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0079
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0080
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0081
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0082
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0083
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0084
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0085
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0086
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0087
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0088
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0089
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0090
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0091
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0092
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0093
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0094
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0095
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0096
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0097
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0098
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0099
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0100

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp02` (the range 1312834712 <= n <= 1629291791 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0051` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0100`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real))
    (n : Nat) (h1 : 1312834712 <= n) (h2 : n <= 1629291791) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1791373280619079820717 : Real) / 2 ^ 40 <= Chebyshev.theta (1629291792 : Real)) := by
  have hb0 := hbase
  have hb1 : (1450350197800578706952 : Real) / 2 ^ 40 <= Chebyshev.theta (1319137944 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0051 hb0 1312834712 le_rfl (by norm_num)).2
  have hb2 : (1457274662552499340397 : Real) / 2 ^ 40 <= Chebyshev.theta (1325438604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0052 hb1 1319137944 le_rfl (by norm_num)).2
  have hb3 : (1464200694941053938497 : Real) / 2 ^ 40 <= Chebyshev.theta (1331745384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0053 hb2 1325438604 le_rfl (by norm_num)).2
  have hb4 : (1471128286020223866789 : Real) / 2 ^ 40 <= Chebyshev.theta (1338027630 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0054 hb3 1331745384 le_rfl (by norm_num)).2
  have hb5 : (1478057428528997661228 : Real) / 2 ^ 40 <= Chebyshev.theta (1344329634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0055 hb4 1338027630 le_rfl (by norm_num)).2
  have hb6 : (1484988116544545347350 : Real) / 2 ^ 40 <= Chebyshev.theta (1350636362 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0056 hb5 1344329634 le_rfl (by norm_num)).2
  have hb7 : (1491920343087186163592 : Real) / 2 ^ 40 <= Chebyshev.theta (1356932868 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0057 hb6 1350636362 le_rfl (by norm_num)).2
  have hb8 : (1498854100024378877110 : Real) / 2 ^ 40 <= Chebyshev.theta (1363237788 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0058 hb7 1356932868 le_rfl (by norm_num)).2
  have hb9 : (1505789382100151474878 : Real) / 2 ^ 40 <= Chebyshev.theta (1369548488 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0059 hb8 1363237788 le_rfl (by norm_num)).2
  have hb10 : (1512726183491404972201 : Real) / 2 ^ 40 <= Chebyshev.theta (1375861784 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0060 hb9 1369548488 le_rfl (by norm_num)).2
  have hb11 : (1519664498414672288900 : Real) / 2 ^ 40 <= Chebyshev.theta (1382174804 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0061 hb10 1375861784 le_rfl (by norm_num)).2
  have hb12 : (1526604319192713930870 : Real) / 2 ^ 40 <= Chebyshev.theta (1388491484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0062 hb11 1382174804 le_rfl (by norm_num)).2
  have hb13 : (1533545638950045693021 : Real) / 2 ^ 40 <= Chebyshev.theta (1394799492 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0063 hb12 1388491484 le_rfl (by norm_num)).2
  have hb14 : (1540488450651911491083 : Real) / 2 ^ 40 <= Chebyshev.theta (1401114432 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0064 hb13 1394799492 le_rfl (by norm_num)).2
  have hb15 : (1547432749493733679899 : Real) / 2 ^ 40 <= Chebyshev.theta (1407434844 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0065 hb14 1401114432 le_rfl (by norm_num)).2
  have hb16 : (1554378528654359115971 : Real) / 2 ^ 40 <= Chebyshev.theta (1413755000 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0066 hb15 1407434844 le_rfl (by norm_num)).2
  have hb17 : (1561325781016046600407 : Real) / 2 ^ 40 <= Chebyshev.theta (1420068212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0067 hb16 1413755000 le_rfl (by norm_num)).2
  have hb18 : (1568274499862025611462 : Real) / 2 ^ 40 <= Chebyshev.theta (1426389510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0068 hb17 1420068212 le_rfl (by norm_num)).2
  have hb19 : (1575224679966652776655 : Real) / 2 ^ 40 <= Chebyshev.theta (1432709204 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0069 hb18 1426389510 le_rfl (by norm_num)).2
  have hb20 : (1582176314993847135932 : Real) / 2 ^ 40 <= Chebyshev.theta (1439039490 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0070 hb19 1432709204 le_rfl (by norm_num)).2
  have hb21 : (1589129399491523871760 : Real) / 2 ^ 40 <= Chebyshev.theta (1445363082 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0071 hb20 1439039490 le_rfl (by norm_num)).2
  have hb22 : (1596083925887198242347 : Real) / 2 ^ 40 <= Chebyshev.theta (1451685338 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0072 hb21 1445363082 le_rfl (by norm_num)).2
  have hb23 : (1603039889391922086008 : Real) / 2 ^ 40 <= Chebyshev.theta (1458009348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0073 hb22 1451685338 le_rfl (by norm_num)).2
  have hb24 : (1609997282679375025621 : Real) / 2 ^ 40 <= Chebyshev.theta (1464330348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0074 hb23 1458009348 le_rfl (by norm_num)).2
  have hb25 : (1616956101313202604001 : Real) / 2 ^ 40 <= Chebyshev.theta (1470672450 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0075 hb24 1464330348 le_rfl (by norm_num)).2
  have hb26 : (1623916339763916847376 : Real) / 2 ^ 40 <= Chebyshev.theta (1476996090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0076 hb25 1470672450 le_rfl (by norm_num)).2
  have hb27 : (1630877989664162140276 : Real) / 2 ^ 40 <= Chebyshev.theta (1483326624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0077 hb26 1476996090 le_rfl (by norm_num)).2
  have hb28 : (1637841046731273946315 : Real) / 2 ^ 40 <= Chebyshev.theta (1489653312 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0078 hb27 1483326624 le_rfl (by norm_num)).2
  have hb29 : (1644805503782574284083 : Real) / 2 ^ 40 <= Chebyshev.theta (1495978692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0079 hb28 1489653312 le_rfl (by norm_num)).2
  have hb30 : (1651771355918220085362 : Real) / 2 ^ 40 <= Chebyshev.theta (1502316924 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0080 hb29 1495978692 le_rfl (by norm_num)).2
  have hb31 : (1658738598744465841953 : Real) / 2 ^ 40 <= Chebyshev.theta (1508645000 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0081 hb30 1502316924 le_rfl (by norm_num)).2
  have hb32 : (1665707227340443109063 : Real) / 2 ^ 40 <= Chebyshev.theta (1514993154 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0082 hb31 1508645000 le_rfl (by norm_num)).2
  have hb33 : (1672677235331555413799 : Real) / 2 ^ 40 <= Chebyshev.theta (1521331314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0083 hb32 1514993154 le_rfl (by norm_num)).2
  have hb34 : (1679648617072023982752 : Real) / 2 ^ 40 <= Chebyshev.theta (1527670014 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0084 hb33 1521331314 le_rfl (by norm_num)).2
  have hb35 : (1686621366226139986428 : Real) / 2 ^ 40 <= Chebyshev.theta (1534008002 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0085 hb34 1527670014 le_rfl (by norm_num)).2
  have hb36 : (1693595479309086806589 : Real) / 2 ^ 40 <= Chebyshev.theta (1540356492 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0086 hb35 1534008002 le_rfl (by norm_num)).2
  have hb37 : (1700570950607916103956 : Real) / 2 ^ 40 <= Chebyshev.theta (1546696290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0087 hb36 1540356492 le_rfl (by norm_num)).2
  have hb38 : (1707547773441023694594 : Real) / 2 ^ 40 <= Chebyshev.theta (1553041200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0088 hb37 1546696290 le_rfl (by norm_num)).2
  have hb39 : (1714525943222644701945 : Real) / 2 ^ 40 <= Chebyshev.theta (1559385392 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0089 hb38 1553041200 le_rfl (by norm_num)).2
  have hb40 : (1721505456371394627752 : Real) / 2 ^ 40 <= Chebyshev.theta (1565747804 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0090 hb39 1559385392 le_rfl (by norm_num)).2
  have hb41 : (1728486307393510031892 : Real) / 2 ^ 40 <= Chebyshev.theta (1572099120 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0091 hb40 1565747804 le_rfl (by norm_num)).2
  have hb42 : (1735468490529898385789 : Real) / 2 ^ 40 <= Chebyshev.theta (1578441902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0092 hb41 1572099120 le_rfl (by norm_num)).2
  have hb43 : (1742451998495359739074 : Real) / 2 ^ 40 <= Chebyshev.theta (1584789674 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0093 hb42 1578441902 le_rfl (by norm_num)).2
  have hb44 : (1749436828015889435091 : Real) / 2 ^ 40 <= Chebyshev.theta (1591146048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0094 hb43 1584789674 le_rfl (by norm_num)).2
  have hb45 : (1756422973999625037262 : Real) / 2 ^ 40 <= Chebyshev.theta (1597498700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0095 hb44 1591146048 le_rfl (by norm_num)).2
  have hb46 : (1763410431714926489963 : Real) / 2 ^ 40 <= Chebyshev.theta (1603851300 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0096 hb45 1597498700 le_rfl (by norm_num)).2
  have hb47 : (1770399195479360159739 : Real) / 2 ^ 40 <= Chebyshev.theta (1610211740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0097 hb46 1603851300 le_rfl (by norm_num)).2
  have hb48 : (1777389261846997071751 : Real) / 2 ^ 40 <= Chebyshev.theta (1616570604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0098 hb47 1610211740 le_rfl (by norm_num)).2
  have hb49 : (1784380625263044374226 : Real) / 2 ^ 40 <= Chebyshev.theta (1622928570 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0099 hb48 1616570604 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0100 hb49 1622928570 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 1470672450 with hc25 | hc25
  · rcases Nat.lt_or_ge n 1388491484 with hc12 | hc12
    · rcases Nat.lt_or_ge n 1350636362 with hc6 | hc6
      · rcases Nat.lt_or_ge n 1331745384 with hc3 | hc3
        · rcases Nat.lt_or_ge n 1319137944 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0051 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1325438604 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0052 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0053 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1338027630 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0054 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1344329634 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0055 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0056 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1369548488 with hc9 | hc9
        · rcases Nat.lt_or_ge n 1356932868 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0057 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1363237788 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0058 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0059 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1375861784 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0060 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1382174804 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0061 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0062 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1426389510 with hc18 | hc18
      · rcases Nat.lt_or_ge n 1407434844 with hc15 | hc15
        · rcases Nat.lt_or_ge n 1394799492 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0063 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1401114432 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0064 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0065 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1413755000 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0066 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1420068212 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0067 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0068 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1445363082 with hc21 | hc21
        · rcases Nat.lt_or_ge n 1432709204 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0069 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1439039490 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0070 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0071 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1458009348 with hc23 | hc23
          · rcases Nat.lt_or_ge n 1451685338 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0072 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0073 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1464330348 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0074 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0075 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 1546696290 with hc37 | hc37
    · rcases Nat.lt_or_ge n 1508645000 with hc31 | hc31
      · rcases Nat.lt_or_ge n 1489653312 with hc28 | hc28
        · rcases Nat.lt_or_ge n 1476996090 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0076 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1483326624 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0077 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0078 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1495978692 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0079 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1502316924 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0080 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0081 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1527670014 with hc34 | hc34
        · rcases Nat.lt_or_ge n 1514993154 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0082 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1521331314 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0083 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0084 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1534008002 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0085 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1540356492 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0086 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0087 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1584789674 with hc43 | hc43
      · rcases Nat.lt_or_ge n 1565747804 with hc40 | hc40
        · rcases Nat.lt_or_ge n 1553041200 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0088 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1559385392 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0089 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0090 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1572099120 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0091 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1578441902 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0092 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0093 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1603851300 with hc46 | hc46
        · rcases Nat.lt_or_ge n 1591146048 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0094 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1597498700 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0095 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0096 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1616570604 with hc48 | hc48
          · rcases Nat.lt_or_ge n 1610211740 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0097 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0098 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1622928570 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0099 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0100 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real))
    (n : Nat) (h1 : 1312834712 <= n) (h2 : n <= 1629291791) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1791373280619079820717 : Real) / 2 ^ 40 <= Chebyshev.theta (1629291792 : Real)) :=
  TFPLink.blk hbase n h1 h2
