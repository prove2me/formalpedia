-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:27:55.712601+00:00
-- url     : https://prove2.me/submissions/5d5a717a-eb80-4ebb-bf41-19eabea3497c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0851
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0852
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0853
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0854
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0855
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0856
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0857
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0858
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0859
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0860
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0861
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0862
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0863
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0864
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0865
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0866
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0867
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0868
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0869
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0870
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0871
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0872
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0873
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0874
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0875
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0876
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0877
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0878
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0879
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0880
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0881
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0882
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0883
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0884
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0885
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0886
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0887
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0888
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0889
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0890
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0891
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0892
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0893
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0894
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0895
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0896
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0897
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0898
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0899
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0900

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp18` (the range 6590693514 <= n <= 6930050749 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0851` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0900`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (7246450329781067871514 : Real) / 2 ^ 40 <= Chebyshev.theta (6590693514 : Real))
    (n : Nat) (h1 : 6590693514 <= n) (h2 : n <= 6930050749) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7619570092620144083607 : Real) / 2 ^ 40 <= Chebyshev.theta (6930050750 : Real)) := by
  have hb0 := hbase
  have hb1 : (7253904552026670296476 : Real) / 2 ^ 40 <= Chebyshev.theta (6597463028 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0851 hb0 6590693514 le_rfl (by norm_num)).2
  have hb2 : (7261359112361630493794 : Real) / 2 ^ 40 <= Chebyshev.theta (6604236698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0852 hb1 6597463028 le_rfl (by norm_num)).2
  have hb3 : (7268814011393079470211 : Real) / 2 ^ 40 <= Chebyshev.theta (6611020370 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0853 hb2 6604236698 le_rfl (by norm_num)).2
  have hb4 : (7276269248609523772605 : Real) / 2 ^ 40 <= Chebyshev.theta (6617803412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0854 hb3 6611020370 le_rfl (by norm_num)).2
  have hb5 : (7283724823596968154268 : Real) / 2 ^ 40 <= Chebyshev.theta (6624579140 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0855 hb4 6617803412 le_rfl (by norm_num)).2
  have hb6 : (7291180735948487849111 : Real) / 2 ^ 40 <= Chebyshev.theta (6631355232 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0856 hb5 6624579140 le_rfl (by norm_num)).2
  have hb7 : (7298636985380147240741 : Real) / 2 ^ 40 <= Chebyshev.theta (6638140254 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0857 hb6 6631355232 le_rfl (by norm_num)).2
  have hb8 : (7306093571571541917998 : Real) / 2 ^ 40 <= Chebyshev.theta (6644922134 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0858 hb7 6638140254 le_rfl (by norm_num)).2
  have hb9 : (7313550494441733484336 : Real) / 2 ^ 40 <= Chebyshev.theta (6651706658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0859 hb8 6644922134 le_rfl (by norm_num)).2
  have hb10 : (7321007753334283633964 : Real) / 2 ^ 40 <= Chebyshev.theta (6658482794 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0860 hb9 6651706658 le_rfl (by norm_num)).2
  have hb11 : (7328465348446979758904 : Real) / 2 ^ 40 <= Chebyshev.theta (6665284940 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0861 hb10 6658482794 le_rfl (by norm_num)).2
  have hb12 : (7335923279238744026607 : Real) / 2 ^ 40 <= Chebyshev.theta (6672057920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0862 hb11 6665284940 le_rfl (by norm_num)).2
  have hb13 : (7343381544927916198233 : Real) / 2 ^ 40 <= Chebyshev.theta (6678839024 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0863 hb12 6672057920 le_rfl (by norm_num)).2
  have hb14 : (7350840145159297655371 : Real) / 2 ^ 40 <= Chebyshev.theta (6685612758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0864 hb13 6678839024 le_rfl (by norm_num)).2
  have hb15 : (7358299079748125575559 : Real) / 2 ^ 40 <= Chebyshev.theta (6692395008 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0865 hb14 6685612758 le_rfl (by norm_num)).2
  have hb16 : (7365758348499403545965 : Real) / 2 ^ 40 <= Chebyshev.theta (6699188558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0866 hb15 6692395008 le_rfl (by norm_num)).2
  have hb17 : (7373217951533143671815 : Real) / 2 ^ 40 <= Chebyshev.theta (6705973092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0867 hb16 6699188558 le_rfl (by norm_num)).2
  have hb18 : (7380677888004237453988 : Real) / 2 ^ 40 <= Chebyshev.theta (6712762430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0868 hb17 6705973092 le_rfl (by norm_num)).2
  have hb19 : (7388138158300072804234 : Real) / 2 ^ 40 <= Chebyshev.theta (6719559212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0869 hb18 6712762430 le_rfl (by norm_num)).2
  have hb20 : (7395598761646990290729 : Real) / 2 ^ 40 <= Chebyshev.theta (6726336048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0870 hb19 6719559212 le_rfl (by norm_num)).2
  have hb21 : (7403059697169738839086 : Real) / 2 ^ 40 <= Chebyshev.theta (6733113770 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0871 hb20 6726336048 le_rfl (by norm_num)).2
  have hb22 : (7410520965164162243582 : Real) / 2 ^ 40 <= Chebyshev.theta (6739915272 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0872 hb21 6733113770 le_rfl (by norm_num)).2
  have hb23 : (7417982565460755034665 : Real) / 2 ^ 40 <= Chebyshev.theta (6746703452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0873 hb22 6739915272 le_rfl (by norm_num)).2
  have hb24 : (7425444497223898042466 : Real) / 2 ^ 40 <= Chebyshev.theta (6753475700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0874 hb23 6746703452 le_rfl (by norm_num)).2
  have hb25 : (7432906759999033789364 : Real) / 2 ^ 40 <= Chebyshev.theta (6760259484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0875 hb24 6753475700 le_rfl (by norm_num)).2
  have hb26 : (7440369353636379725426 : Real) / 2 ^ 40 <= Chebyshev.theta (6767052324 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0876 hb25 6760259484 le_rfl (by norm_num)).2
  have hb27 : (7447832277945218939248 : Real) / 2 ^ 40 <= Chebyshev.theta (6773836274 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0877 hb26 6767052324 le_rfl (by norm_num)).2
  have hb28 : (7455295532481413608857 : Real) / 2 ^ 40 <= Chebyshev.theta (6780609860 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0878 hb27 6773836274 le_rfl (by norm_num)).2
  have hb29 : (7462759116691047397423 : Real) / 2 ^ 40 <= Chebyshev.theta (6787405698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0879 hb28 6780609860 le_rfl (by norm_num)).2
  have hb30 : (7470223030697853715760 : Real) / 2 ^ 40 <= Chebyshev.theta (6794188104 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0880 hb29 6787405698 le_rfl (by norm_num)).2
  have hb31 : (7477687274287299296697 : Real) / 2 ^ 40 <= Chebyshev.theta (6800985938 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0881 hb30 6794188104 le_rfl (by norm_num)).2
  have hb32 : (7485151847405797339762 : Real) / 2 ^ 40 <= Chebyshev.theta (6807783894 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0882 hb31 6800985938 le_rfl (by norm_num)).2
  have hb33 : (7492616749153350088406 : Real) / 2 ^ 40 <= Chebyshev.theta (6814568240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0883 hb32 6807783894 le_rfl (by norm_num)).2
  have hb34 : (7500081979589498432042 : Real) / 2 ^ 40 <= Chebyshev.theta (6821356724 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0884 hb33 6814568240 le_rfl (by norm_num)).2
  have hb35 : (7507547537942629656920 : Real) / 2 ^ 40 <= Chebyshev.theta (6828141962 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0885 hb34 6821356724 le_rfl (by norm_num)).2
  have hb36 : (7515013423954857285766 : Real) / 2 ^ 40 <= Chebyshev.theta (6834935670 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0886 hb35 6828141962 le_rfl (by norm_num)).2
  have hb37 : (7522479637696327928920 : Real) / 2 ^ 40 <= Chebyshev.theta (6841725462 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0887 hb36 6834935670 le_rfl (by norm_num)).2
  have hb38 : (7529946178981720568081 : Real) / 2 ^ 40 <= Chebyshev.theta (6848525238 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0888 hb37 6841725462 le_rfl (by norm_num)).2
  have hb39 : (7537413047272004088773 : Real) / 2 ^ 40 <= Chebyshev.theta (6855323192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0889 hb38 6848525238 le_rfl (by norm_num)).2
  have hb40 : (7544880242265194542498 : Real) / 2 ^ 40 <= Chebyshev.theta (6862111914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0890 hb39 6855323192 le_rfl (by norm_num)).2
  have hb41 : (7552347764040927868848 : Real) / 2 ^ 40 <= Chebyshev.theta (6868909740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0891 hb40 6862111914 le_rfl (by norm_num)).2
  have hb42 : (7559815611709812032200 : Real) / 2 ^ 40 <= Chebyshev.theta (6875698020 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0892 hb41 6868909740 le_rfl (by norm_num)).2
  have hb43 : (7567283785196862724949 : Real) / 2 ^ 40 <= Chebyshev.theta (6882499544 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0893 hb42 6875698020 le_rfl (by norm_num)).2
  have hb44 : (7574752284275452436762 : Real) / 2 ^ 40 <= Chebyshev.theta (6889298618 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0894 hb43 6882499544 le_rfl (by norm_num)).2
  have hb45 : (7582221108618106275862 : Real) / 2 ^ 40 <= Chebyshev.theta (6896088078 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0895 hb44 6889298618 le_rfl (by norm_num)).2
  have hb46 : (7589690257442791872851 : Real) / 2 ^ 40 <= Chebyshev.theta (6902874614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0896 hb45 6896088078 le_rfl (by norm_num)).2
  have hb47 : (7597159730265181305401 : Real) / 2 ^ 40 <= Chebyshev.theta (6909659634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0897 hb46 6902874614 le_rfl (by norm_num)).2
  have hb48 : (7604629527151141682427 : Real) / 2 ^ 40 <= Chebyshev.theta (6916452480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0898 hb47 6909659634 le_rfl (by norm_num)).2
  have hb49 : (7612099648021037064337 : Real) / 2 ^ 40 <= Chebyshev.theta (6923250194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0899 hb48 6916452480 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0900 hb49 6923250194 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 6760259484 with hc25 | hc25
  · rcases Nat.lt_or_ge n 6672057920 with hc12 | hc12
    · rcases Nat.lt_or_ge n 6631355232 with hc6 | hc6
      · rcases Nat.lt_or_ge n 6611020370 with hc3 | hc3
        · rcases Nat.lt_or_ge n 6597463028 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0851 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6604236698 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0852 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0853 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6617803412 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0854 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6624579140 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0855 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0856 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6651706658 with hc9 | hc9
        · rcases Nat.lt_or_ge n 6638140254 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0857 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6644922134 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0858 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0859 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6658482794 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0860 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6665284940 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0861 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0862 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6712762430 with hc18 | hc18
      · rcases Nat.lt_or_ge n 6692395008 with hc15 | hc15
        · rcases Nat.lt_or_ge n 6678839024 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0863 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6685612758 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0864 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0865 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6699188558 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0866 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6705973092 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0867 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0868 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6733113770 with hc21 | hc21
        · rcases Nat.lt_or_ge n 6719559212 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0869 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6726336048 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0870 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0871 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6746703452 with hc23 | hc23
          · rcases Nat.lt_or_ge n 6739915272 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0872 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0873 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6753475700 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0874 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0875 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 6841725462 with hc37 | hc37
    · rcases Nat.lt_or_ge n 6800985938 with hc31 | hc31
      · rcases Nat.lt_or_ge n 6780609860 with hc28 | hc28
        · rcases Nat.lt_or_ge n 6767052324 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0876 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6773836274 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0877 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0878 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6787405698 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0879 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6794188104 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0880 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0881 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6821356724 with hc34 | hc34
        · rcases Nat.lt_or_ge n 6807783894 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0882 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6814568240 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0883 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0884 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6828141962 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0885 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6834935670 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0886 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0887 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6882499544 with hc43 | hc43
      · rcases Nat.lt_or_ge n 6862111914 with hc40 | hc40
        · rcases Nat.lt_or_ge n 6848525238 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0888 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6855323192 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0889 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0890 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6868909740 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0891 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6875698020 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0892 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0893 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6902874614 with hc46 | hc46
        · rcases Nat.lt_or_ge n 6889298618 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0894 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6896088078 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0895 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0896 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6916452480 with hc48 | hc48
          · rcases Nat.lt_or_ge n 6909659634 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0897 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0898 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6923250194 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0899 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0900 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (7246450329781067871514 : Real) / 2 ^ 40 <= Chebyshev.theta (6590693514 : Real))
    (n : Nat) (h1 : 6590693514 <= n) (h2 : n <= 6930050749) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7619570092620144083607 : Real) / 2 ^ 40 <= Chebyshev.theta (6930050750 : Real)) :=
  TFPLink.blk hbase n h1 h2
