-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:23:51.144004+00:00
-- url     : https://prove2.me/submissions/97e18616-d3b4-4dd7-80e0-952c604791cf

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert001
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert002
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert003
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert004
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert005
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert006
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert007
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert008
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert009
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert010
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert011
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert012
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert013
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert014
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert015
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert016
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert017
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert018
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert019
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert020
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert021
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert022
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert023
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert024
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert025
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert026
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert027
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert028
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert029
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert030
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert031
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert032
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert033
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert034
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert035
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert036
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert037
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert038
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert039
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert040
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert041
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert042
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert043
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert044
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert045
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert046
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert047
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert048
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert049
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert050
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert051

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp01` (the range 100000000 <= n <= 393128003 with its carry in and carry out) from the 51 Phase 1 certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert001` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert051`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (109929172545044480000 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real))
    (n : Nat) (h1 : 100000000 <= n) (h2 : n <= 393128003) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real)) := by
  have hb0 := hbase
  have hb1 : (115985490414503642521 : Real) / 2 ^ 40 <= Chebyshev.theta (105505290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert001 hb0 100000000 le_rfl (by norm_num)).2
  have hb2 : (122058970791088291864 : Real) / 2 ^ 40 <= Chebyshev.theta (111026058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert002 hb1 105505290 le_rfl (by norm_num)).2
  have hb3 : (128148815562481517540 : Real) / 2 ^ 40 <= Chebyshev.theta (116568182 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert003 hb2 111026058 le_rfl (by norm_num)).2
  have hb4 : (134254294163458731240 : Real) / 2 ^ 40 <= Chebyshev.theta (122125308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert004 hb3 116568182 le_rfl (by norm_num)).2
  have hb5 : (140374725612029200054 : Real) / 2 ^ 40 <= Chebyshev.theta (127690208 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert005 hb4 122125308 le_rfl (by norm_num)).2
  have hb6 : (146509482822057092842 : Real) / 2 ^ 40 <= Chebyshev.theta (133269860 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert006 hb5 127690208 le_rfl (by norm_num)).2
  have hb7 : (152658009984549557155 : Real) / 2 ^ 40 <= Chebyshev.theta (138864182 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert007 hb6 133269860 le_rfl (by norm_num)).2
  have hb8 : (158819777702852284624 : Real) / 2 ^ 40 <= Chebyshev.theta (144462408 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert008 hb7 138864182 le_rfl (by norm_num)).2
  have hb9 : (164994290069456348378 : Real) / 2 ^ 40 <= Chebyshev.theta (150081180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert009 hb8 144462408 le_rfl (by norm_num)).2
  have hb10 : (171181110267650324692 : Real) / 2 ^ 40 <= Chebyshev.theta (155710602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert010 hb9 150081180 le_rfl (by norm_num)).2
  have hb11 : (177379807665904808287 : Real) / 2 ^ 40 <= Chebyshev.theta (161348330 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert011 hb10 155710602 le_rfl (by norm_num)).2
  have hb12 : (183589991146815588247 : Real) / 2 ^ 40 <= Chebyshev.theta (166998614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert012 hb11 161348330 le_rfl (by norm_num)).2
  have hb13 : (189811285027837642575 : Real) / 2 ^ 40 <= Chebyshev.theta (172650912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert013 hb12 166998614 le_rfl (by norm_num)).2
  have hb14 : (196043343088932618867 : Real) / 2 ^ 40 <= Chebyshev.theta (178316108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert014 hb13 172650912 le_rfl (by norm_num)).2
  have hb15 : (202285846417560768081 : Real) / 2 ^ 40 <= Chebyshev.theta (183999360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert015 hb14 178316108 le_rfl (by norm_num)).2
  have hb16 : (208538489905179355987 : Real) / 2 ^ 40 <= Chebyshev.theta (189683538 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert016 hb15 183999360 le_rfl (by norm_num)).2
  have hb17 : (214800989614683467040 : Real) / 2 ^ 40 <= Chebyshev.theta (195379782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert017 hb16 189683538 le_rfl (by norm_num)).2
  have hb18 : (221073073202695746290 : Real) / 2 ^ 40 <= Chebyshev.theta (201089412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert018 hb17 195379782 le_rfl (by norm_num)).2
  have hb19 : (227354479870817296173 : Real) / 2 ^ 40 <= Chebyshev.theta (206801942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert019 hb18 201089412 le_rfl (by norm_num)).2
  have hb20 : (233644962155203533963 : Real) / 2 ^ 40 <= Chebyshev.theta (212522868 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert020 hb19 206801942 le_rfl (by norm_num)).2
  have hb21 : (239944291182350139519 : Real) / 2 ^ 40 <= Chebyshev.theta (218252720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert021 hb20 212522868 le_rfl (by norm_num)).2
  have hb22 : (246252248086832042087 : Real) / 2 ^ 40 <= Chebyshev.theta (223991180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert022 hb21 218252720 le_rfl (by norm_num)).2
  have hb23 : (252568618446463043437 : Real) / 2 ^ 40 <= Chebyshev.theta (229737948 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert023 hb22 223991180 le_rfl (by norm_num)).2
  have hb24 : (258893205654435319143 : Real) / 2 ^ 40 <= Chebyshev.theta (235488864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert024 hb23 229737948 le_rfl (by norm_num)).2
  have hb25 : (265225813164412260592 : Real) / 2 ^ 40 <= Chebyshev.theta (241240752 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert025 hb24 235488864 le_rfl (by norm_num)).2
  have hb26 : (271566262903548526280 : Real) / 2 ^ 40 <= Chebyshev.theta (247010948 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert026 hb25 241240752 le_rfl (by norm_num)).2
  have hb27 : (277914381258425326537 : Real) / 2 ^ 40 <= Chebyshev.theta (252784854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert027 hb26 247010948 le_rfl (by norm_num)).2
  have hb28 : (284270002542376905498 : Real) / 2 ^ 40 <= Chebyshev.theta (258564542 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert028 hb27 252784854 le_rfl (by norm_num)).2
  have hb29 : (290632967016128098646 : Real) / 2 ^ 40 <= Chebyshev.theta (264352070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert029 hb28 258564542 le_rfl (by norm_num)).2
  have hb30 : (297003124359028185652 : Real) / 2 ^ 40 <= Chebyshev.theta (270147678 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert030 hb29 264352070 le_rfl (by norm_num)).2
  have hb31 : (303380331745508031739 : Real) / 2 ^ 40 <= Chebyshev.theta (275946488 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert031 hb30 270147678 le_rfl (by norm_num)).2
  have hb32 : (309764439977448747312 : Real) / 2 ^ 40 <= Chebyshev.theta (281750150 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert032 hb31 275946488 le_rfl (by norm_num)).2
  have hb33 : (316155320080910923937 : Real) / 2 ^ 40 <= Chebyshev.theta (287568014 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert033 hb32 281750150 le_rfl (by norm_num)).2
  have hb34 : (322552841604596834596 : Real) / 2 ^ 40 <= Chebyshev.theta (293386730 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert034 hb33 287568014 le_rfl (by norm_num)).2
  have hb35 : (328956876406464935138 : Real) / 2 ^ 40 <= Chebyshev.theta (299212862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert035 hb34 293386730 le_rfl (by norm_num)).2
  have hb36 : (335367306052801765654 : Real) / 2 ^ 40 <= Chebyshev.theta (305039744 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert036 hb35 299212862 le_rfl (by norm_num)).2
  have hb37 : (341784010687424805078 : Real) / 2 ^ 40 <= Chebyshev.theta (310872278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert037 hb36 305039744 le_rfl (by norm_num)).2
  have hb38 : (348206880615548571972 : Real) / 2 ^ 40 <= Chebyshev.theta (316715072 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert038 hb37 310872278 le_rfl (by norm_num)).2
  have hb39 : (354635812711236209502 : Real) / 2 ^ 40 <= Chebyshev.theta (322566954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert039 hb38 316715072 le_rfl (by norm_num)).2
  have hb40 : (361070700599478951623 : Real) / 2 ^ 40 <= Chebyshev.theta (328418628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert040 hb39 322566954 le_rfl (by norm_num)).2
  have hb41 : (367511443486110023181 : Real) / 2 ^ 40 <= Chebyshev.theta (334280034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert041 hb40 328418628 le_rfl (by norm_num)).2
  have hb42 : (373957943387292629365 : Real) / 2 ^ 40 <= Chebyshev.theta (340142490 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert042 hb41 334280034 le_rfl (by norm_num)).2
  have hb43 : (380410102409431635883 : Real) / 2 ^ 40 <= Chebyshev.theta (346007568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert043 hb42 340142490 le_rfl (by norm_num)).2
  have hb44 : (386867832720225827742 : Real) / 2 ^ 40 <= Chebyshev.theta (351884064 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert044 hb43 346007568 le_rfl (by norm_num)).2
  have hb45 : (393331045319442231038 : Real) / 2 ^ 40 <= Chebyshev.theta (357761984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert045 hb44 351884064 le_rfl (by norm_num)).2
  have hb46 : (399799657437801949047 : Real) / 2 ^ 40 <= Chebyshev.theta (363647564 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert046 hb45 357761984 le_rfl (by norm_num)).2
  have hb47 : (406273582622677813668 : Real) / 2 ^ 40 <= Chebyshev.theta (369536114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert047 hb46 363647564 le_rfl (by norm_num)).2
  have hb48 : (412752744404589158745 : Real) / 2 ^ 40 <= Chebyshev.theta (375427754 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert048 hb47 369536114 le_rfl (by norm_num)).2
  have hb49 : (419237053352189757959 : Real) / 2 ^ 40 <= Chebyshev.theta (381314304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert049 hb48 375427754 le_rfl (by norm_num)).2
  have hb50 : (425726438872312599762 : Real) / 2 ^ 40 <= Chebyshev.theta (387220200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert050 hb49 381314304 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert051 hb50 387220200 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 241240752 with hc25 | hc25
  · rcases Nat.lt_or_ge n 166998614 with hc12 | hc12
    · rcases Nat.lt_or_ge n 133269860 with hc6 | hc6
      · rcases Nat.lt_or_ge n 116568182 with hc3 | hc3
        · rcases Nat.lt_or_ge n 105505290 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert001 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 111026058 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert002 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert003 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 122125308 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert004 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 127690208 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert005 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert006 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 150081180 with hc9 | hc9
        · rcases Nat.lt_or_ge n 138864182 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert007 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 144462408 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert008 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert009 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 155710602 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert010 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 161348330 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert011 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert012 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 201089412 with hc18 | hc18
      · rcases Nat.lt_or_ge n 183999360 with hc15 | hc15
        · rcases Nat.lt_or_ge n 172650912 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert013 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 178316108 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert014 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert015 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 189683538 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert016 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 195379782 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert017 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert018 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 218252720 with hc21 | hc21
        · rcases Nat.lt_or_ge n 206801942 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert019 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 212522868 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert020 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert021 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 229737948 with hc23 | hc23
          · rcases Nat.lt_or_ge n 223991180 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert022 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert023 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 235488864 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert024 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert025 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 316715072 with hc38 | hc38
    · rcases Nat.lt_or_ge n 275946488 with hc31 | hc31
      · rcases Nat.lt_or_ge n 258564542 with hc28 | hc28
        · rcases Nat.lt_or_ge n 247010948 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert026 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 252784854 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert027 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert028 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 264352070 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert029 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 270147678 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert030 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert031 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 293386730 with hc34 | hc34
        · rcases Nat.lt_or_ge n 281750150 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert032 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 287568014 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert033 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert034 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 305039744 with hc36 | hc36
          · rcases Nat.lt_or_ge n 299212862 with hc35 | hc35
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert035 hb34 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert036 hb35 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 310872278 with hc37 | hc37
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert037 hb36 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert038 hb37 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 351884064 with hc44 | hc44
      · rcases Nat.lt_or_ge n 334280034 with hc41 | hc41
        · rcases Nat.lt_or_ge n 322566954 with hc39 | hc39
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert039 hb38 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 328418628 with hc40 | hc40
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert040 hb39 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert041 hb40 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 340142490 with hc42 | hc42
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert042 hb41 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 346007568 with hc43 | hc43
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert043 hb42 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert044 hb43 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 369536114 with hc47 | hc47
        · rcases Nat.lt_or_ge n 357761984 with hc45 | hc45
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert045 hb44 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 363647564 with hc46 | hc46
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert046 hb45 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert047 hb46 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 381314304 with hc49 | hc49
          · rcases Nat.lt_or_ge n 375427754 with hc48 | hc48
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert048 hb47 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert049 hb48 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 387220200 with hc50 | hc50
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert050 hb49 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert051 hb50 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (109929172545044480000 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real))
    (n : Nat) (h1 : 100000000 <= n) (h2 : n <= 393128003) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real)) :=
  TFPLink.blk hbase n h1 h2
