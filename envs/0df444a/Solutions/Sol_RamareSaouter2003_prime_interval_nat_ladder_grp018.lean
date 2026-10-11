-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T00:40:43.950416+00:00
-- url     : https://prove2.me/submissions/07e88ec7-878d-4de1-97d5-bf14253bf8c6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00900

theorem solution (n : Nat)
    (hn : 71627919427 < n) (hupper : n <= 80362118567) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 75866622691 n with h2 | h2
  · -- n > 75866622691
    rcases Nat.lt_or_ge 77991456343 n with h4 | h4
    · -- n > 77991456343
      rcases Nat.lt_or_ge 79076593571 n with h6 | h6
      · -- n > 79076593571
        rcases Nat.lt_or_ge 79624938641 n with h8 | h8
        · -- n > 79624938641
          rcases Nat.lt_or_ge 79992660403 n with h10 | h10
          · -- n > 79992660403
            rcases Nat.lt_or_ge 80177171911 n with h12 | h12
            · -- n > 80177171911
              exact RamareSaouter2003.prime_interval_nat_ladder_c00900 n (by omega) (by omega)
            · -- n <= 80177171911
              exact RamareSaouter2003.prime_interval_nat_ladder_c00899 n (by omega) (by omega)
          · -- n <= 79992660403
            rcases Nat.lt_or_ge 79808582983 n with h12 | h12
            · -- n > 79808582983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00898 n (by omega) (by omega)
            · -- n <= 79808582983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00897 n (by omega) (by omega)
        · -- n <= 79624938641
          rcases Nat.lt_or_ge 79258944953 n with h10 | h10
          · -- n > 79258944953
            rcases Nat.lt_or_ge 79441726303 n with h12 | h12
            · -- n > 79441726303
              exact RamareSaouter2003.prime_interval_nat_ladder_c00896 n (by omega) (by omega)
            · -- n <= 79441726303
              exact RamareSaouter2003.prime_interval_nat_ladder_c00895 n (by omega) (by omega)
          · -- n <= 79258944953
            exact RamareSaouter2003.prime_interval_nat_ladder_c00894 n (by omega) (by omega)
      · -- n <= 79076593571
        rcases Nat.lt_or_ge 78532108679 n with h8 | h8
        · -- n > 78532108679
          rcases Nat.lt_or_ge 78713176417 n with h10 | h10
          · -- n > 78713176417
            rcases Nat.lt_or_ge 78894671041 n with h12 | h12
            · -- n > 78894671041
              exact RamareSaouter2003.prime_interval_nat_ladder_c00893 n (by omega) (by omega)
            · -- n <= 78894671041
              exact RamareSaouter2003.prime_interval_nat_ladder_c00892 n (by omega) (by omega)
          · -- n <= 78713176417
            exact RamareSaouter2003.prime_interval_nat_ladder_c00891 n (by omega) (by omega)
        · -- n <= 78532108679
          rcases Nat.lt_or_ge 78171249703 n with h10 | h10
          · -- n > 78171249703
            rcases Nat.lt_or_ge 78351466729 n with h12 | h12
            · -- n > 78351466729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00890 n (by omega) (by omega)
            · -- n <= 78351466729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00889 n (by omega) (by omega)
          · -- n <= 78171249703
            exact RamareSaouter2003.prime_interval_nat_ladder_c00888 n (by omega) (by omega)
    · -- n <= 77991456343
      rcases Nat.lt_or_ge 76921538581 n with h6 | h6
      · -- n > 76921538581
        rcases Nat.lt_or_ge 77454608713 n with h8 | h8
        · -- n > 77454608713
          rcases Nat.lt_or_ge 77633136859 n with h10 | h10
          · -- n > 77633136859
            rcases Nat.lt_or_ge 77812085731 n with h12 | h12
            · -- n > 77812085731
              exact RamareSaouter2003.prime_interval_nat_ladder_c00887 n (by omega) (by omega)
            · -- n <= 77812085731
              exact RamareSaouter2003.prime_interval_nat_ladder_c00886 n (by omega) (by omega)
          · -- n <= 77633136859
            exact RamareSaouter2003.prime_interval_nat_ladder_c00885 n (by omega) (by omega)
        · -- n <= 77454608713
          rcases Nat.lt_or_ge 77098810583 n with h10 | h10
          · -- n > 77098810583
            rcases Nat.lt_or_ge 77276500291 n with h12 | h12
            · -- n > 77276500291
              exact RamareSaouter2003.prime_interval_nat_ladder_c00884 n (by omega) (by omega)
            · -- n <= 77276500291
              exact RamareSaouter2003.prime_interval_nat_ladder_c00883 n (by omega) (by omega)
          · -- n <= 77098810583
            exact RamareSaouter2003.prime_interval_nat_ladder_c00882 n (by omega) (by omega)
      · -- n <= 76921538581
        rcases Nat.lt_or_ge 76392218921 n with h8 | h8
        · -- n > 76392218921
          rcases Nat.lt_or_ge 76568243711 n with h10 | h10
          · -- n > 76568243711
            rcases Nat.lt_or_ge 76744683293 n with h12 | h12
            · -- n > 76744683293
              exact RamareSaouter2003.prime_interval_nat_ladder_c00881 n (by omega) (by omega)
            · -- n <= 76744683293
              exact RamareSaouter2003.prime_interval_nat_ladder_c00880 n (by omega) (by omega)
          · -- n <= 76568243711
            exact RamareSaouter2003.prime_interval_nat_ladder_c00879 n (by omega) (by omega)
        · -- n <= 76392218921
          rcases Nat.lt_or_ge 76041409393 n with h10 | h10
          · -- n > 76041409393
            rcases Nat.lt_or_ge 76216607767 n with h12 | h12
            · -- n > 76216607767
              exact RamareSaouter2003.prime_interval_nat_ladder_c00878 n (by omega) (by omega)
            · -- n <= 76216607767
              exact RamareSaouter2003.prime_interval_nat_ladder_c00877 n (by omega) (by omega)
          · -- n <= 76041409393
            exact RamareSaouter2003.prime_interval_nat_ladder_c00876 n (by omega) (by omega)
  · -- n <= 75866622691
    rcases Nat.lt_or_ge 73631416967 n with h4 | h4
    · -- n > 73631416967
      rcases Nat.lt_or_ge 74654561747 n with h6 | h6
      · -- n > 74654561747
        rcases Nat.lt_or_ge 75171573703 n with h8 | h8
        · -- n > 75171573703
          rcases Nat.lt_or_ge 75518280731 n with h10 | h10
          · -- n > 75518280731
            rcases Nat.lt_or_ge 75692246827 n with h12 | h12
            · -- n > 75692246827
              exact RamareSaouter2003.prime_interval_nat_ladder_c00875 n (by omega) (by omega)
            · -- n <= 75692246827
              exact RamareSaouter2003.prime_interval_nat_ladder_c00874 n (by omega) (by omega)
          · -- n <= 75518280731
            rcases Nat.lt_or_ge 75344723347 n with h12 | h12
            · -- n > 75344723347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00873 n (by omega) (by omega)
            · -- n <= 75344723347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00872 n (by omega) (by omega)
        · -- n <= 75171573703
          rcases Nat.lt_or_ge 74826493879 n with h10 | h10
          · -- n > 74826493879
            rcases Nat.lt_or_ge 74998830869 n with h12 | h12
            · -- n > 74998830869
              exact RamareSaouter2003.prime_interval_nat_ladder_c00871 n (by omega) (by omega)
            · -- n <= 74998830869
              exact RamareSaouter2003.prime_interval_nat_ladder_c00870 n (by omega) (by omega)
          · -- n <= 74826493879
            exact RamareSaouter2003.prime_interval_nat_ladder_c00869 n (by omega) (by omega)
      · -- n <= 74654561747
        rcases Nat.lt_or_ge 74141184899 n with h8 | h8
        · -- n > 74141184899
          rcases Nat.lt_or_ge 74311908193 n with h10 | h10
          · -- n > 74311908193
            rcases Nat.lt_or_ge 74483033501 n with h12 | h12
            · -- n > 74483033501
              exact RamareSaouter2003.prime_interval_nat_ladder_c00868 n (by omega) (by omega)
            · -- n <= 74483033501
              exact RamareSaouter2003.prime_interval_nat_ladder_c00867 n (by omega) (by omega)
          · -- n <= 74311908193
            exact RamareSaouter2003.prime_interval_nat_ladder_c00866 n (by omega) (by omega)
        · -- n <= 74141184899
          rcases Nat.lt_or_ge 73800940217 n with h10 | h10
          · -- n > 73800940217
            rcases Nat.lt_or_ge 73970862527 n with h12 | h12
            · -- n > 73970862527
              exact RamareSaouter2003.prime_interval_nat_ladder_c00865 n (by omega) (by omega)
            · -- n <= 73970862527
              exact RamareSaouter2003.prime_interval_nat_ladder_c00864 n (by omega) (by omega)
          · -- n <= 73800940217
            exact RamareSaouter2003.prime_interval_nat_ladder_c00863 n (by omega) (by omega)
    · -- n <= 73631416967
      rcases Nat.lt_or_ge 72622604653 n with h6 | h6
      · -- n > 72622604653
        rcases Nat.lt_or_ge 73125232123 n with h8 | h8
        · -- n > 73125232123
          rcases Nat.lt_or_ge 73293563881 n with h10 | h10
          · -- n > 73293563881
            rcases Nat.lt_or_ge 73462291849 n with h12 | h12
            · -- n > 73462291849
              exact RamareSaouter2003.prime_interval_nat_ladder_c00862 n (by omega) (by omega)
            · -- n <= 73462291849
              exact RamareSaouter2003.prime_interval_nat_ladder_c00861 n (by omega) (by omega)
          · -- n <= 73293563881
            exact RamareSaouter2003.prime_interval_nat_ladder_c00860 n (by omega) (by omega)
        · -- n <= 73125232123
          rcases Nat.lt_or_ge 72789753461 n with h10 | h10
          · -- n > 72789753461
            rcases Nat.lt_or_ge 72957295627 n with h12 | h12
            · -- n > 72957295627
              exact RamareSaouter2003.prime_interval_nat_ladder_c00859 n (by omega) (by omega)
            · -- n <= 72957295627
              exact RamareSaouter2003.prime_interval_nat_ladder_c00858 n (by omega) (by omega)
          · -- n <= 72789753461
            exact RamareSaouter2003.prime_interval_nat_ladder_c00857 n (by omega) (by omega)
      · -- n <= 72622604653
        rcases Nat.lt_or_ge 72123508819 n with h8 | h8
        · -- n > 72123508819
          rcases Nat.lt_or_ge 72289483243 n with h10 | h10
          · -- n > 72289483243
            rcases Nat.lt_or_ge 72455848217 n with h12 | h12
            · -- n > 72455848217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00856 n (by omega) (by omega)
            · -- n <= 72455848217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00855 n (by omega) (by omega)
          · -- n <= 72289483243
            exact RamareSaouter2003.prime_interval_nat_ladder_c00854 n (by omega) (by omega)
        · -- n <= 72123508819
          rcases Nat.lt_or_ge 71792727869 n with h10 | h10
          · -- n > 71792727869
            rcases Nat.lt_or_ge 71957923979 n with h12 | h12
            · -- n > 71957923979
              exact RamareSaouter2003.prime_interval_nat_ladder_c00853 n (by omega) (by omega)
            · -- n <= 71957923979
              exact RamareSaouter2003.prime_interval_nat_ladder_c00852 n (by omega) (by omega)
          · -- n <= 71792727869
            exact RamareSaouter2003.prime_interval_nat_ladder_c00851 n (by omega) (by omega)
