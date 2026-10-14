-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T13:43:09.058069+00:00
-- url     : https://prove2.me/submissions/f7488e46-eee6-4631-9da0-33d6136dcedf

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04950

theorem solution (n : Nat)
    (hn : 2345869641159829 < n) (hupper : n <= 2701984647071959) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2517646750880171 n with h2 | h2
  · -- n > 2517646750880171
    rcases Nat.lt_or_ge 2604496621192091 n with h4 | h4
    · -- n > 2604496621192091
      rcases Nat.lt_or_ge 2649048596925529 n with h6 | h6
      · -- n > 2649048596925529
        rcases Nat.lt_or_ge 2671606964215373 n with h8 | h8
        · -- n > 2671606964215373
          rcases Nat.lt_or_ge 2686752879500891 n with h10 | h10
          · -- n > 2686752879500891
            rcases Nat.lt_or_ge 2694358658770673 n with h12 | h12
            · -- n > 2694358658770673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04950 n (by omega) (by omega)
            · -- n <= 2694358658770673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04949 n (by omega) (by omega)
          · -- n <= 2686752879500891
            rcases Nat.lt_or_ge 2679168928273949 n with h12 | h12
            · -- n > 2679168928273949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04948 n (by omega) (by omega)
            · -- n <= 2679168928273949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04947 n (by omega) (by omega)
        · -- n <= 2671606964215373
          rcases Nat.lt_or_ge 2656547769416549 n with h10 | h10
          · -- n > 2656547769416549
            rcases Nat.lt_or_ge 2664064871834543 n with h12 | h12
            · -- n > 2664064871834543
              exact RamareSaouter2003.prime_interval_nat_ladder_c04946 n (by omega) (by omega)
            · -- n <= 2664064871834543
              exact RamareSaouter2003.prime_interval_nat_ladder_c04945 n (by omega) (by omega)
          · -- n <= 2656547769416549
            exact RamareSaouter2003.prime_interval_nat_ladder_c04944 n (by omega) (by omega)
      · -- n <= 2649048596925529
        rcases Nat.lt_or_ge 2626678949607157 n with h8 | h8
        · -- n > 2626678949607157
          rcases Nat.lt_or_ge 2634115724013031 n with h10 | h10
          · -- n > 2634115724013031
            rcases Nat.lt_or_ge 2641571231413159 n with h12 | h12
            · -- n > 2641571231413159
              exact RamareSaouter2003.prime_interval_nat_ladder_c04943 n (by omega) (by omega)
            · -- n <= 2641571231413159
              exact RamareSaouter2003.prime_interval_nat_ladder_c04942 n (by omega) (by omega)
          · -- n <= 2634115724013031
            exact RamareSaouter2003.prime_interval_nat_ladder_c04941 n (by omega) (by omega)
        · -- n <= 2626678949607157
          rcases Nat.lt_or_ge 2611870060452839 n with h10 | h10
          · -- n > 2611870060452839
            rcases Nat.lt_or_ge 2619264359603909 n with h12 | h12
            · -- n > 2619264359603909
              exact RamareSaouter2003.prime_interval_nat_ladder_c04940 n (by omega) (by omega)
            · -- n <= 2619264359603909
              exact RamareSaouter2003.prime_interval_nat_ladder_c04939 n (by omega) (by omega)
          · -- n <= 2611870060452839
            exact RamareSaouter2003.prime_interval_nat_ladder_c04938 n (by omega) (by omega)
    · -- n <= 2604496621192091
      rcases Nat.lt_or_ge 2560705827018973 n with h6 | h6
      · -- n > 2560705827018973
        rcases Nat.lt_or_ge 2582508263504467 n with h8 | h8
        · -- n > 2582508263504467
          rcases Nat.lt_or_ge 2589817863281911 n with h10 | h10
          · -- n > 2589817863281911
            rcases Nat.lt_or_ge 2597144309092391 n with h12 | h12
            · -- n > 2597144309092391
              exact RamareSaouter2003.prime_interval_nat_ladder_c04937 n (by omega) (by omega)
            · -- n <= 2597144309092391
              exact RamareSaouter2003.prime_interval_nat_ladder_c04936 n (by omega) (by omega)
          · -- n <= 2589817863281911
            exact RamareSaouter2003.prime_interval_nat_ladder_c04935 n (by omega) (by omega)
        · -- n <= 2582508263504467
          rcases Nat.lt_or_ge 2567955641836811 n with h10 | h10
          · -- n > 2567955641836811
            rcases Nat.lt_or_ge 2575224632154407 n with h12 | h12
            · -- n > 2575224632154407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04934 n (by omega) (by omega)
            · -- n <= 2575224632154407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04933 n (by omega) (by omega)
          · -- n <= 2567955641836811
            exact RamareSaouter2003.prime_interval_nat_ladder_c04932 n (by omega) (by omega)
      · -- n <= 2560705827018973
        rcases Nat.lt_or_ge 2539082885162171 n with h8 | h8
        · -- n > 2539082885162171
          rcases Nat.lt_or_ge 2546270858632981 n with h10 | h10
          · -- n > 2546270858632981
            rcases Nat.lt_or_ge 2553476875140431 n with h12 | h12
            · -- n > 2553476875140431
              exact RamareSaouter2003.prime_interval_nat_ladder_c04931 n (by omega) (by omega)
            · -- n <= 2553476875140431
              exact RamareSaouter2003.prime_interval_nat_ladder_c04930 n (by omega) (by omega)
          · -- n <= 2546270858632981
            exact RamareSaouter2003.prime_interval_nat_ladder_c04929 n (by omega) (by omega)
        · -- n <= 2539082885162171
          rcases Nat.lt_or_ge 2524773085937693 n with h10 | h10
          · -- n > 2524773085937693
            rcases Nat.lt_or_ge 2531914727385431 n with h12 | h12
            · -- n > 2531914727385431
              exact RamareSaouter2003.prime_interval_nat_ladder_c04928 n (by omega) (by omega)
            · -- n <= 2531914727385431
              exact RamareSaouter2003.prime_interval_nat_ladder_c04927 n (by omega) (by omega)
          · -- n <= 2524773085937693
            exact RamareSaouter2003.prime_interval_nat_ladder_c04926 n (by omega) (by omega)
  · -- n <= 2517646750880171
    rcases Nat.lt_or_ge 2426809703535983 n with h4 | h4
    · -- n > 2426809703535983
      rcases Nat.lt_or_ge 2468320329063619 n with h6 | h6
      · -- n > 2468320329063619
        rcases Nat.lt_or_ge 2489342505380567 n with h8 | h8
        · -- n > 2489342505380567
          rcases Nat.lt_or_ge 2503454215643027 n with h10 | h10
          · -- n > 2503454215643027
            rcases Nat.lt_or_ge 2510539106014943 n with h12 | h12
            · -- n > 2510539106014943
              exact RamareSaouter2003.prime_interval_nat_ladder_c04925 n (by omega) (by omega)
            · -- n <= 2510539106014943
              exact RamareSaouter2003.prime_interval_nat_ladder_c04924 n (by omega) (by omega)
          · -- n <= 2503454215643027
            rcases Nat.lt_or_ge 2496389729470859 n with h12 | h12
            · -- n > 2496389729470859
              exact RamareSaouter2003.prime_interval_nat_ladder_c04923 n (by omega) (by omega)
            · -- n <= 2496389729470859
              exact RamareSaouter2003.prime_interval_nat_ladder_c04922 n (by omega) (by omega)
        · -- n <= 2489342505380567
          rcases Nat.lt_or_ge 2475308299241797 n with h10 | h10
          · -- n > 2475308299241797
            rcases Nat.lt_or_ge 2482315312934731 n with h12 | h12
            · -- n > 2482315312934731
              exact RamareSaouter2003.prime_interval_nat_ladder_c04921 n (by omega) (by omega)
            · -- n <= 2482315312934731
              exact RamareSaouter2003.prime_interval_nat_ladder_c04920 n (by omega) (by omega)
          · -- n <= 2475308299241797
            exact RamareSaouter2003.prime_interval_nat_ladder_c04919 n (by omega) (by omega)
      · -- n <= 2468320329063619
        rcases Nat.lt_or_ge 2447480099880251 n with h8 | h8
        · -- n > 2447480099880251
          rcases Nat.lt_or_ge 2454408208827139 n with h10 | h10
          · -- n > 2454408208827139
            rcases Nat.lt_or_ge 2461354539575341 n with h12 | h12
            · -- n > 2461354539575341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04918 n (by omega) (by omega)
            · -- n <= 2461354539575341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04917 n (by omega) (by omega)
          · -- n <= 2454408208827139
            exact RamareSaouter2003.prime_interval_nat_ladder_c04916 n (by omega) (by omega)
        · -- n <= 2447480099880251
          rcases Nat.lt_or_ge 2433680493758023 n with h10 | h10
          · -- n > 2433680493758023
            rcases Nat.lt_or_ge 2440570480056977 n with h12 | h12
            · -- n > 2440570480056977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04915 n (by omega) (by omega)
            · -- n <= 2440570480056977
              exact RamareSaouter2003.prime_interval_nat_ladder_c04914 n (by omega) (by omega)
          · -- n <= 2433680493758023
            exact RamareSaouter2003.prime_interval_nat_ladder_c04913 n (by omega) (by omega)
    · -- n <= 2426809703535983
      rcases Nat.lt_or_ge 2385992614753841 n with h6 | h6
      · -- n > 2385992614753841
        rcases Nat.lt_or_ge 2406315750704053 n with h8 | h8
        · -- n > 2406315750704053
          rcases Nat.lt_or_ge 2413128601569131 n with h10 | h10
          · -- n > 2413128601569131
            rcases Nat.lt_or_ge 2419959643433693 n with h12 | h12
            · -- n > 2419959643433693
              exact RamareSaouter2003.prime_interval_nat_ladder_c04912 n (by omega) (by omega)
            · -- n <= 2419959643433693
              exact RamareSaouter2003.prime_interval_nat_ladder_c04911 n (by omega) (by omega)
          · -- n <= 2413128601569131
            exact RamareSaouter2003.prime_interval_nat_ladder_c04910 n (by omega) (by omega)
        · -- n <= 2406315750704053
          rcases Nat.lt_or_ge 2392747896369653 n with h10 | h10
          · -- n > 2392747896369653
            rcases Nat.lt_or_ge 2399522423347747 n with h12 | h12
            · -- n > 2399522423347747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04909 n (by omega) (by omega)
            · -- n <= 2399522423347747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04908 n (by omega) (by omega)
          · -- n <= 2392747896369653
            exact RamareSaouter2003.prime_interval_nat_ladder_c04907 n (by omega) (by omega)
      · -- n <= 2385992614753841
        rcases Nat.lt_or_ge 2365846527192761 n with h8 | h8
        · -- n > 2365846527192761
          rcases Nat.lt_or_ge 2372541097622737 n with h10 | h10
          · -- n > 2372541097622737
            rcases Nat.lt_or_ge 2379258398097923 n with h12 | h12
            · -- n > 2379258398097923
              exact RamareSaouter2003.prime_interval_nat_ladder_c04906 n (by omega) (by omega)
            · -- n <= 2379258398097923
              exact RamareSaouter2003.prime_interval_nat_ladder_c04905 n (by omega) (by omega)
          · -- n <= 2372541097622737
            exact RamareSaouter2003.prime_interval_nat_ladder_c04904 n (by omega) (by omega)
        · -- n <= 2365846527192761
          rcases Nat.lt_or_ge 2352508552559941 n with h10 | h10
          · -- n > 2352508552559941
            rcases Nat.lt_or_ge 2359168990663231 n with h12 | h12
            · -- n > 2359168990663231
              exact RamareSaouter2003.prime_interval_nat_ladder_c04903 n (by omega) (by omega)
            · -- n <= 2359168990663231
              exact RamareSaouter2003.prime_interval_nat_ladder_c04902 n (by omega) (by omega)
          · -- n <= 2352508552559941
            exact RamareSaouter2003.prime_interval_nat_ladder_c04901 n (by omega) (by omega)
