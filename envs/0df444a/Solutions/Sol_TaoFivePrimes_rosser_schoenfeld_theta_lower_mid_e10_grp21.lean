-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:44:53.321039+00:00
-- url     : https://prove2.me/submissions/8efff317-592c-4044-a737-6b46b0172d7e

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1001
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1002
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1003
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1004
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1005
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1006
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1007
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1008
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1009
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1010
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1011
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1012
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1013
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1014
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1015
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1016
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1017
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1018
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1019
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1020
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1021
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1022
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1023
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1024
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1025
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1026
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1027
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1028
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1029
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1030
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1031
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1032
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1033
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1034
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1035
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1036
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1037
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1038
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1039
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1040
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1041
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1042
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1043
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1044
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1045
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1046
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1047
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1048
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1049
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1050

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp21` (the range 7610969534 <= n <= 7952421523 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1001` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1050`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (8368198731656839134845 : Real) / 2 ^ 40 <= Chebyshev.theta (7610969534 : Real))
    (n : Nat) (h1 : 7610969534 <= n) (h2 : n <= 7952421523) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((8743638325656144631277 : Real) / 2 ^ 40 <= Chebyshev.theta (7952421524 : Real)) := by
  have hb0 := hbase
  have hb1 : (8375700386127145713507 : Real) / 2 ^ 40 <= Chebyshev.theta (7617796890 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1001 hb0 7610969534 le_rfl (by norm_num)).2
  have hb2 : (8383202335612883944318 : Real) / 2 ^ 40 <= Chebyshev.theta (7624603620 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1002 hb1 7617796890 le_rfl (by norm_num)).2
  have hb3 : (8390704579791230567486 : Real) / 2 ^ 40 <= Chebyshev.theta (7631429720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1003 hb2 7624603620 le_rfl (by norm_num)).2
  have hb4 : (8398207118785174732707 : Real) / 2 ^ 40 <= Chebyshev.theta (7638249398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1004 hb3 7631429720 le_rfl (by norm_num)).2
  have hb5 : (8405709952445492085887 : Real) / 2 ^ 40 <= Chebyshev.theta (7645081040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1005 hb4 7638249398 le_rfl (by norm_num)).2
  have hb6 : (8413213080604165679710 : Real) / 2 ^ 40 <= Chebyshev.theta (7651906740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1006 hb5 7645081040 le_rfl (by norm_num)).2
  have hb7 : (8420716502801986404571 : Real) / 2 ^ 40 <= Chebyshev.theta (7658736518 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1007 hb6 7651906740 le_rfl (by norm_num)).2
  have hb8 : (8428220218966760932055 : Real) / 2 ^ 40 <= Chebyshev.theta (7665558222 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1008 hb7 7658736518 le_rfl (by norm_num)).2
  have hb9 : (8435724228463820594065 : Real) / 2 ^ 40 <= Chebyshev.theta (7672375032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1009 hb8 7665558222 le_rfl (by norm_num)).2
  have hb10 : (8443228531248695788819 : Real) / 2 ^ 40 <= Chebyshev.theta (7679209650 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1010 hb9 7672375032 le_rfl (by norm_num)).2
  have hb11 : (8450733127400464260070 : Real) / 2 ^ 40 <= Chebyshev.theta (7686043680 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1011 hb10 7679209650 le_rfl (by norm_num)).2
  have hb12 : (8458238016279619642455 : Real) / 2 ^ 40 <= Chebyshev.theta (7692860888 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1012 hb11 7686043680 le_rfl (by norm_num)).2
  have hb13 : (8465743197650045096392 : Real) / 2 ^ 40 <= Chebyshev.theta (7699689510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1013 hb12 7692860888 le_rfl (by norm_num)).2
  have hb14 : (8473248671524020930322 : Real) / 2 ^ 40 <= Chebyshev.theta (7706526380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1014 hb13 7699689510 le_rfl (by norm_num)).2
  have hb15 : (8480754437753811312386 : Real) / 2 ^ 40 <= Chebyshev.theta (7713354950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1015 hb14 7706526380 le_rfl (by norm_num)).2
  have hb16 : (8488260495544917499466 : Real) / 2 ^ 40 <= Chebyshev.theta (7720171118 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1016 hb15 7713354950 le_rfl (by norm_num)).2
  have hb17 : (8495766844780676561366 : Real) / 2 ^ 40 <= Chebyshev.theta (7727002398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1017 hb16 7720171118 le_rfl (by norm_num)).2
  have hb18 : (8503273485402664000348 : Real) / 2 ^ 40 <= Chebyshev.theta (7733830550 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1018 hb17 7727002398 le_rfl (by norm_num)).2
  have hb19 : (8510780417047866456266 : Real) / 2 ^ 40 <= Chebyshev.theta (7740655100 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1019 hb18 7733830550 le_rfl (by norm_num)).2
  have hb20 : (8518287639473096608920 : Real) / 2 ^ 40 <= Chebyshev.theta (7747486782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1020 hb19 7740655100 le_rfl (by norm_num)).2
  have hb21 : (8525795152698635573766 : Real) / 2 ^ 40 <= Chebyshev.theta (7754317392 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1021 hb20 7747486782 le_rfl (by norm_num)).2
  have hb22 : (8533302956223595618609 : Real) / 2 ^ 40 <= Chebyshev.theta (7761144212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1022 hb21 7754317392 le_rfl (by norm_num)).2
  have hb23 : (8540811049679753555478 : Real) / 2 ^ 40 <= Chebyshev.theta (7767970118 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1023 hb22 7761144212 le_rfl (by norm_num)).2
  have hb24 : (8548319432810153233496 : Real) / 2 ^ 40 <= Chebyshev.theta (7774795434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1024 hb23 7767970118 le_rfl (by norm_num)).2
  have hb25 : (8555828105334022146019 : Real) / 2 ^ 40 <= Chebyshev.theta (7781616458 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1025 hb24 7774795434 le_rfl (by norm_num)).2
  have hb26 : (8563337067031617198054 : Real) / 2 ^ 40 <= Chebyshev.theta (7788447464 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1026 hb25 7781616458 le_rfl (by norm_num)).2
  have hb27 : (8570846318118029852609 : Real) / 2 ^ 40 <= Chebyshev.theta (7795282322 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1027 hb26 7788447464 le_rfl (by norm_num)).2
  have hb28 : (8578355858211640221596 : Real) / 2 ^ 40 <= Chebyshev.theta (7802116200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1028 hb27 7795282322 le_rfl (by norm_num)).2
  have hb29 : (8585865686953714446295 : Real) / 2 ^ 40 <= Chebyshev.theta (7808944938 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1029 hb28 7802116200 le_rfl (by norm_num)).2
  have hb30 : (8593375804203587175465 : Real) / 2 ^ 40 <= Chebyshev.theta (7815779894 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1030 hb29 7808944938 le_rfl (by norm_num)).2
  have hb31 : (8600886209461114938028 : Real) / 2 ^ 40 <= Chebyshev.theta (7822603208 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1031 hb30 7815779894 le_rfl (by norm_num)).2
  have hb32 : (8608396902212199366950 : Real) / 2 ^ 40 <= Chebyshev.theta (7829427314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1032 hb31 7822603208 le_rfl (by norm_num)).2
  have hb33 : (8615907882222026079604 : Real) / 2 ^ 40 <= Chebyshev.theta (7836250022 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1033 hb32 7829427314 le_rfl (by norm_num)).2
  have hb34 : (8623419149558508902978 : Real) / 2 ^ 40 <= Chebyshev.theta (7843082384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1034 hb33 7836250022 le_rfl (by norm_num)).2
  have hb35 : (8630930704003951460152 : Real) / 2 ^ 40 <= Chebyshev.theta (7849908954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1035 hb34 7843082384 le_rfl (by norm_num)).2
  have hb36 : (8638442545549794748272 : Real) / 2 ^ 40 <= Chebyshev.theta (7856743442 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1036 hb35 7849908954 le_rfl (by norm_num)).2
  have hb37 : (8645954673945780966520 : Real) / 2 ^ 40 <= Chebyshev.theta (7863580890 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1037 hb36 7856743442 le_rfl (by norm_num)).2
  have hb38 : (8653467088590919262373 : Real) / 2 ^ 40 <= Chebyshev.theta (7870410774 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1038 hb37 7863580890 le_rfl (by norm_num)).2
  have hb39 : (8660979789583638168643 : Real) / 2 ^ 40 <= Chebyshev.theta (7877247504 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1039 hb38 7870410774 le_rfl (by norm_num)).2
  have hb40 : (8668492776967476960715 : Real) / 2 ^ 40 <= Chebyshev.theta (7884087560 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1040 hb39 7877247504 le_rfl (by norm_num)).2
  have hb41 : (8676006050089904703666 : Real) / 2 ^ 40 <= Chebyshev.theta (7890920492 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1041 hb40 7884087560 le_rfl (by norm_num)).2
  have hb42 : (8683519608811558503212 : Real) / 2 ^ 40 <= Chebyshev.theta (7897757450 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1042 hb41 7890920492 le_rfl (by norm_num)).2
  have hb43 : (8691033452725699658542 : Real) / 2 ^ 40 <= Chebyshev.theta (7904581964 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1043 hb42 7897757450 le_rfl (by norm_num)).2
  have hb44 : (8698547581116907170291 : Real) / 2 ^ 40 <= Chebyshev.theta (7911403430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1044 hb43 7904581964 le_rfl (by norm_num)).2
  have hb45 : (8706061994272279764602 : Real) / 2 ^ 40 <= Chebyshev.theta (7918250598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1045 hb44 7911403430 le_rfl (by norm_num)).2
  have hb46 : (8713576692280570579758 : Real) / 2 ^ 40 <= Chebyshev.theta (7925085032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1046 hb45 7918250598 le_rfl (by norm_num)).2
  have hb47 : (8721091674776905602819 : Real) / 2 ^ 40 <= Chebyshev.theta (7931922228 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1047 hb46 7925085032 le_rfl (by norm_num)).2
  have hb48 : (8728606941314356032620 : Real) / 2 ^ 40 <= Chebyshev.theta (7938759168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1048 hb47 7931922228 le_rfl (by norm_num)).2
  have hb49 : (8736122491704065610551 : Real) / 2 ^ 40 <= Chebyshev.theta (7945589498 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1049 hb48 7938759168 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1050 hb49 7945589498 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 7781616458 with hc25 | hc25
  · rcases Nat.lt_or_ge n 7692860888 with hc12 | hc12
    · rcases Nat.lt_or_ge n 7651906740 with hc6 | hc6
      · rcases Nat.lt_or_ge n 7631429720 with hc3 | hc3
        · rcases Nat.lt_or_ge n 7617796890 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1001 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7624603620 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1002 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1003 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7638249398 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1004 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7645081040 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1005 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1006 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7672375032 with hc9 | hc9
        · rcases Nat.lt_or_ge n 7658736518 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1007 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7665558222 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1008 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1009 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7679209650 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1010 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7686043680 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1011 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1012 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7733830550 with hc18 | hc18
      · rcases Nat.lt_or_ge n 7713354950 with hc15 | hc15
        · rcases Nat.lt_or_ge n 7699689510 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1013 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7706526380 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1014 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1015 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7720171118 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1016 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7727002398 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1017 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1018 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7754317392 with hc21 | hc21
        · rcases Nat.lt_or_ge n 7740655100 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1019 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7747486782 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1020 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1021 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7767970118 with hc23 | hc23
          · rcases Nat.lt_or_ge n 7761144212 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1022 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1023 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7774795434 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1024 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1025 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 7863580890 with hc37 | hc37
    · rcases Nat.lt_or_ge n 7822603208 with hc31 | hc31
      · rcases Nat.lt_or_ge n 7802116200 with hc28 | hc28
        · rcases Nat.lt_or_ge n 7788447464 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1026 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7795282322 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1027 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1028 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7808944938 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1029 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7815779894 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1030 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1031 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7843082384 with hc34 | hc34
        · rcases Nat.lt_or_ge n 7829427314 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1032 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7836250022 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1033 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1034 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7849908954 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1035 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7856743442 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1036 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1037 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7904581964 with hc43 | hc43
      · rcases Nat.lt_or_ge n 7884087560 with hc40 | hc40
        · rcases Nat.lt_or_ge n 7870410774 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1038 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7877247504 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1039 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1040 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7890920492 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1041 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7897757450 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1042 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1043 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7925085032 with hc46 | hc46
        · rcases Nat.lt_or_ge n 7911403430 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1044 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7918250598 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1045 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1046 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7938759168 with hc48 | hc48
          · rcases Nat.lt_or_ge n 7931922228 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1047 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1048 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7945589498 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1049 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1050 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (8368198731656839134845 : Real) / 2 ^ 40 <= Chebyshev.theta (7610969534 : Real))
    (n : Nat) (h1 : 7610969534 <= n) (h2 : n <= 7952421523) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((8743638325656144631277 : Real) / 2 ^ 40 <= Chebyshev.theta (7952421524 : Real)) :=
  TFPLink.blk hbase n h1 h2
