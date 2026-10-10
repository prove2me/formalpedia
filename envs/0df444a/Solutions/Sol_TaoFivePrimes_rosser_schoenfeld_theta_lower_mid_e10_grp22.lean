-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T01:49:17.774982+00:00
-- url     : https://prove2.me/submissions/78868fd8-e1ec-4263-9b8e-7e2e77743a53

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1051
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1052
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1053
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1054
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1055
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1056
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1057
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1058
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1059
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1060
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1061
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1062
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1063
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1064
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1065
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1066
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1067
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1068
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1069
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1070
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1071
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1072
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1073
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1074
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1075
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1076
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1077
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1078
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1079
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1080
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1081
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1082
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1083
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1084
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1085
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1086
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1087
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1088
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1089
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1090
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1091
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1092
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1093
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1094
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1095
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1096
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1097
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1098
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1099
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1100

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp22` (the range 7952421524 <= n <= 8294482073 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1051` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1100`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (8743638325656144631277 : Real) / 2 ^ 40 <= Chebyshev.theta (7952421524 : Real))
    (n : Nat) (h1 : 7952421524 <= n) (h2 : n <= 8294482073) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9119786553842252571751 : Real) / 2 ^ 40 <= Chebyshev.theta (8294482074 : Real)) := by
  have hb0 := hbase
  have hb1 : (8751154443015042521204 : Real) / 2 ^ 40 <= Chebyshev.theta (7959255570 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1051 hb0 7952421524 le_rfl (by norm_num)).2
  have hb2 : (8758670843461657326129 : Real) / 2 ^ 40 <= Chebyshev.theta (7966097732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1052 hb1 7959255570 le_rfl (by norm_num)).2
  have hb3 : (8766187526914306388386 : Real) / 2 ^ 40 <= Chebyshev.theta (7972934760 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1053 hb2 7966097732 le_rfl (by norm_num)).2
  have hb4 : (8773704493013883718697 : Real) / 2 ^ 40 <= Chebyshev.theta (7979758434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1054 hb3 7972934760 le_rfl (by norm_num)).2
  have hb5 : (8781221741120696886420 : Real) / 2 ^ 40 <= Chebyshev.theta (7986595392 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1055 hb4 7979758434 le_rfl (by norm_num)).2
  have hb6 : (8788739271354013735662 : Real) / 2 ^ 40 <= Chebyshev.theta (7993431354 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1056 hb5 7986595392 le_rfl (by norm_num)).2
  have hb7 : (8796257083642013068568 : Real) / 2 ^ 40 <= Chebyshev.theta (8000267600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1057 hb6 7993431354 le_rfl (by norm_num)).2
  have hb8 : (8803775177554511959121 : Real) / 2 ^ 40 <= Chebyshev.theta (8007093218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1058 hb7 8000267600 le_rfl (by norm_num)).2
  have hb9 : (8811293552482518747782 : Real) / 2 ^ 40 <= Chebyshev.theta (8013923552 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1059 hb8 8007093218 le_rfl (by norm_num)).2
  have hb10 : (8818812208805234474008 : Real) / 2 ^ 40 <= Chebyshev.theta (8020764798 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1060 hb9 8013923552 le_rfl (by norm_num)).2
  have hb11 : (8826331146189788352918 : Real) / 2 ^ 40 <= Chebyshev.theta (8027603262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1061 hb10 8020764798 le_rfl (by norm_num)).2
  have hb12 : (8833850364542031353126 : Real) / 2 ^ 40 <= Chebyshev.theta (8034448634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1062 hb11 8027603262 le_rfl (by norm_num)).2
  have hb13 : (8841369863704924378802 : Real) / 2 ^ 40 <= Chebyshev.theta (8041288782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1063 hb12 8034448634 le_rfl (by norm_num)).2
  have hb14 : (8848889643270798402740 : Real) / 2 ^ 40 <= Chebyshev.theta (8048129994 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1064 hb13 8041288782 le_rfl (by norm_num)).2
  have hb15 : (8856409703106058554317 : Real) / 2 ^ 40 <= Chebyshev.theta (8054966090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1065 hb14 8048129994 le_rfl (by norm_num)).2
  have hb16 : (8863930042921187258756 : Real) / 2 ^ 40 <= Chebyshev.theta (8061811212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1066 hb15 8054966090 le_rfl (by norm_num)).2
  have hb17 : (8871450662363590811559 : Real) / 2 ^ 40 <= Chebyshev.theta (8068644164 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1067 hb16 8061811212 le_rfl (by norm_num)).2
  have hb18 : (8878971561303767778251 : Real) / 2 ^ 40 <= Chebyshev.theta (8075481944 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1068 hb17 8068644164 le_rfl (by norm_num)).2
  have hb19 : (8886492739062952019511 : Real) / 2 ^ 40 <= Chebyshev.theta (8082313698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1069 hb18 8075481944 le_rfl (by norm_num)).2
  have hb20 : (8894014195706080317856 : Real) / 2 ^ 40 <= Chebyshev.theta (8089157004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1070 hb19 8082313698 le_rfl (by norm_num)).2
  have hb21 : (8901535931386656528807 : Real) / 2 ^ 40 <= Chebyshev.theta (8096001540 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1071 hb20 8089157004 le_rfl (by norm_num)).2
  have hb22 : (8909057945635237952390 : Real) / 2 ^ 40 <= Chebyshev.theta (8102835530 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1072 hb21 8096001540 le_rfl (by norm_num)).2
  have hb23 : (8916580238255153588259 : Real) / 2 ^ 40 <= Chebyshev.theta (8109684992 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1073 hb22 8102835530 le_rfl (by norm_num)).2
  have hb24 : (8924102809163232256514 : Real) / 2 ^ 40 <= Chebyshev.theta (8116529258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1074 hb23 8109684992 le_rfl (by norm_num)).2
  have hb25 : (8931625658080562103306 : Real) / 2 ^ 40 <= Chebyshev.theta (8123375784 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1075 hb24 8116529258 le_rfl (by norm_num)).2
  have hb26 : (8939148784935694061338 : Real) / 2 ^ 40 <= Chebyshev.theta (8130215364 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1076 hb25 8123375784 le_rfl (by norm_num)).2
  have hb27 : (8946672189424411398760 : Real) / 2 ^ 40 <= Chebyshev.theta (8137073004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1077 hb26 8130215364 le_rfl (by norm_num)).2
  have hb28 : (8954195871152627853762 : Real) / 2 ^ 40 <= Chebyshev.theta (8143899398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1078 hb27 8137073004 le_rfl (by norm_num)).2
  have hb29 : (8961719829766633330170 : Real) / 2 ^ 40 <= Chebyshev.theta (8150750450 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1079 hb28 8143899398 le_rfl (by norm_num)).2
  have hb30 : (8969244065366717013590 : Real) / 2 ^ 40 <= Chebyshev.theta (8157602978 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1080 hb29 8150750450 le_rfl (by norm_num)).2
  have hb31 : (8976768577660570350055 : Real) / 2 ^ 40 <= Chebyshev.theta (8164443800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1081 hb30 8157602978 le_rfl (by norm_num)).2
  have hb32 : (8984293366158097393575 : Real) / 2 ^ 40 <= Chebyshev.theta (8171279630 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1082 hb31 8164443800 le_rfl (by norm_num)).2
  have hb33 : (8991818430850925206577 : Real) / 2 ^ 40 <= Chebyshev.theta (8178137168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1083 hb32 8171279630 le_rfl (by norm_num)).2
  have hb34 : (8999343771745007878001 : Real) / 2 ^ 40 <= Chebyshev.theta (8184977832 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1084 hb33 8178137168 le_rfl (by norm_num)).2
  have hb35 : (9006869388316943776843 : Real) / 2 ^ 40 <= Chebyshev.theta (8191821200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1085 hb34 8184977832 le_rfl (by norm_num)).2
  have hb36 : (9014395280102500030952 : Real) / 2 ^ 40 <= Chebyshev.theta (8198656230 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1086 hb35 8191821200 le_rfl (by norm_num)).2
  have hb37 : (9021921446865745866025 : Real) / 2 ^ 40 <= Chebyshev.theta (8205498450 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1087 hb36 8198656230 le_rfl (by norm_num)).2
  have hb38 : (9029447888407219302525 : Real) / 2 ^ 40 <= Chebyshev.theta (8212336944 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1088 hb37 8205498450 le_rfl (by norm_num)).2
  have hb39 : (9036974604515736248311 : Real) / 2 ^ 40 <= Chebyshev.theta (8219179352 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1089 hb38 8212336944 le_rfl (by norm_num)).2
  have hb40 : (9044501595039467435378 : Real) / 2 ^ 40 <= Chebyshev.theta (8226022830 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1090 hb39 8219179352 le_rfl (by norm_num)).2
  have hb41 : (9052028860201319068469 : Real) / 2 ^ 40 <= Chebyshev.theta (8232871332 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1091 hb40 8226022830 le_rfl (by norm_num)).2
  have hb42 : (9059556399381321636561 : Real) / 2 ^ 40 <= Chebyshev.theta (8239715244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1092 hb41 8232871332 le_rfl (by norm_num)).2
  have hb43 : (9067084212320658335981 : Real) / 2 ^ 40 <= Chebyshev.theta (8246554112 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1093 hb42 8239715244 le_rfl (by norm_num)).2
  have hb44 : (9074612298998303790156 : Real) / 2 ^ 40 <= Chebyshev.theta (8253401438 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1094 hb43 8246554112 le_rfl (by norm_num)).2
  have hb45 : (9082140659229123046063 : Real) / 2 ^ 40 <= Chebyshev.theta (8260253180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1095 hb44 8253401438 le_rfl (by norm_num)).2
  have hb46 : (9089669292905198241640 : Real) / 2 ^ 40 <= Chebyshev.theta (8267098424 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1096 hb45 8260253180 le_rfl (by norm_num)).2
  have hb47 : (9097198199412327889524 : Real) / 2 ^ 40 <= Chebyshev.theta (8273940278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1097 hb46 8267098424 le_rfl (by norm_num)).2
  have hb48 : (9104727378411128920056 : Real) / 2 ^ 40 <= Chebyshev.theta (8280775128 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1098 hb47 8273940278 le_rfl (by norm_num)).2
  have hb49 : (9112256829862527624557 : Real) / 2 ^ 40 <= Chebyshev.theta (8287624230 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1099 hb48 8280775128 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1100 hb49 8287624230 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 8123375784 with hc25 | hc25
  · rcases Nat.lt_or_ge n 8034448634 with hc12 | hc12
    · rcases Nat.lt_or_ge n 7993431354 with hc6 | hc6
      · rcases Nat.lt_or_ge n 7972934760 with hc3 | hc3
        · rcases Nat.lt_or_ge n 7959255570 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1051 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7966097732 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1052 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1053 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7979758434 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1054 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7986595392 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1055 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1056 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8013923552 with hc9 | hc9
        · rcases Nat.lt_or_ge n 8000267600 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1057 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8007093218 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1058 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1059 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8020764798 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1060 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8027603262 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1061 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1062 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8075481944 with hc18 | hc18
      · rcases Nat.lt_or_ge n 8054966090 with hc15 | hc15
        · rcases Nat.lt_or_ge n 8041288782 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1063 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8048129994 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1064 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1065 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8061811212 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1066 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8068644164 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1067 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1068 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8096001540 with hc21 | hc21
        · rcases Nat.lt_or_ge n 8082313698 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1069 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8089157004 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1070 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1071 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8109684992 with hc23 | hc23
          · rcases Nat.lt_or_ge n 8102835530 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1072 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1073 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8116529258 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1074 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1075 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 8205498450 with hc37 | hc37
    · rcases Nat.lt_or_ge n 8164443800 with hc31 | hc31
      · rcases Nat.lt_or_ge n 8143899398 with hc28 | hc28
        · rcases Nat.lt_or_ge n 8130215364 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1076 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8137073004 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1077 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1078 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8150750450 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1079 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8157602978 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1080 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1081 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8184977832 with hc34 | hc34
        · rcases Nat.lt_or_ge n 8171279630 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1082 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8178137168 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1083 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1084 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8191821200 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1085 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8198656230 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1086 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1087 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8246554112 with hc43 | hc43
      · rcases Nat.lt_or_ge n 8226022830 with hc40 | hc40
        · rcases Nat.lt_or_ge n 8212336944 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1088 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8219179352 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1089 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1090 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8232871332 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1091 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8239715244 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1092 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1093 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 8267098424 with hc46 | hc46
        · rcases Nat.lt_or_ge n 8253401438 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1094 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8260253180 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1095 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1096 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8280775128 with hc48 | hc48
          · rcases Nat.lt_or_ge n 8273940278 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1097 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1098 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 8287624230 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1099 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1100 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (8743638325656144631277 : Real) / 2 ^ 40 <= Chebyshev.theta (7952421524 : Real))
    (n : Nat) (h1 : 7952421524 <= n) (h2 : n <= 8294482073) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((9119786553842252571751 : Real) / 2 ^ 40 <= Chebyshev.theta (8294482074 : Real)) :=
  TFPLink.blk hbase n h1 h2
