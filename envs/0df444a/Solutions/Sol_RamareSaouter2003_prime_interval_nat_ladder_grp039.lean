-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T13:21:34.577029+00:00
-- url     : https://prove2.me/submissions/8b0e5520-a08f-4a7d-b31b-f2acaf69e01d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01950

theorem solution (n : Nat)
    (hn : 973153707433 < n) (hupper : n <= 1104932290381) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1036960086947 n with h2 | h2
  · -- n > 1036960086947
    rcases Nat.lt_or_ge 1069051363603 n with h4 | h4
    · -- n > 1069051363603
      rcases Nat.lt_or_ge 1085465470259 n with h6 | h6
      · -- n > 1085465470259
        rcases Nat.lt_or_ge 1093766271583 n with h8 | h8
        · -- n > 1093766271583
          rcases Nat.lt_or_ge 1099335181709 n with h10 | h10
          · -- n > 1099335181709
            rcases Nat.lt_or_ge 1102130202317 n with h12 | h12
            · -- n > 1102130202317
              exact RamareSaouter2003.prime_interval_nat_ladder_c01950 n (by omega) (by omega)
            · -- n <= 1102130202317
              exact RamareSaouter2003.prime_interval_nat_ladder_c01949 n (by omega) (by omega)
          · -- n <= 1099335181709
            rcases Nat.lt_or_ge 1096547210651 n with h12 | h12
            · -- n > 1096547210651
              exact RamareSaouter2003.prime_interval_nat_ladder_c01948 n (by omega) (by omega)
            · -- n <= 1096547210651
              exact RamareSaouter2003.prime_interval_nat_ladder_c01947 n (by omega) (by omega)
        · -- n <= 1093766271583
          rcases Nat.lt_or_ge 1088225418961 n with h10 | h10
          · -- n > 1088225418961
            rcases Nat.lt_or_ge 1090992346879 n with h12 | h12
            · -- n > 1090992346879
              exact RamareSaouter2003.prime_interval_nat_ladder_c01946 n (by omega) (by omega)
            · -- n <= 1090992346879
              exact RamareSaouter2003.prime_interval_nat_ladder_c01945 n (by omega) (by omega)
          · -- n <= 1088225418961
            exact RamareSaouter2003.prime_interval_nat_ladder_c01944 n (by omega) (by omega)
      · -- n <= 1085465470259
        rcases Nat.lt_or_ge 1077227324347 n with h8 | h8
        · -- n > 1077227324347
          rcases Nat.lt_or_ge 1079966440369 n with h10 | h10
          · -- n > 1079966440369
            rcases Nat.lt_or_ge 1082712483169 n with h12 | h12
            · -- n > 1082712483169
              exact RamareSaouter2003.prime_interval_nat_ladder_c01943 n (by omega) (by omega)
            · -- n <= 1082712483169
              exact RamareSaouter2003.prime_interval_nat_ladder_c01942 n (by omega) (by omega)
          · -- n <= 1079966440369
            exact RamareSaouter2003.prime_interval_nat_ladder_c01941 n (by omega) (by omega)
        · -- n <= 1077227324347
          rcases Nat.lt_or_ge 1071769803319 n with h10 | h10
          · -- n > 1071769803319
            rcases Nat.lt_or_ge 1074495117841 n with h12 | h12
            · -- n > 1074495117841
              exact RamareSaouter2003.prime_interval_nat_ladder_c01940 n (by omega) (by omega)
            · -- n <= 1074495117841
              exact RamareSaouter2003.prime_interval_nat_ladder_c01939 n (by omega) (by omega)
          · -- n <= 1071769803319
            exact RamareSaouter2003.prime_interval_nat_ladder_c01938 n (by omega) (by omega)
    · -- n <= 1069051363603
      rcases Nat.lt_or_ge 1052884133363 n with h6 | h6
      · -- n > 1052884133363
        rcases Nat.lt_or_ge 1060937121089 n with h8 | h8
        · -- n > 1060937121089
          rcases Nat.lt_or_ge 1063635039647 n with h10 | h10
          · -- n > 1063635039647
            rcases Nat.lt_or_ge 1066339781411 n with h12 | h12
            · -- n > 1066339781411
              exact RamareSaouter2003.prime_interval_nat_ladder_c01937 n (by omega) (by omega)
            · -- n <= 1066339781411
              exact RamareSaouter2003.prime_interval_nat_ladder_c01936 n (by omega) (by omega)
          · -- n <= 1063635039647
            exact RamareSaouter2003.prime_interval_nat_ladder_c01935 n (by omega) (by omega)
        · -- n <= 1060937121089
          rcases Nat.lt_or_ge 1055561684963 n with h10 | h10
          · -- n > 1055561684963
            rcases Nat.lt_or_ge 1058246008531 n with h12 | h12
            · -- n > 1058246008531
              exact RamareSaouter2003.prime_interval_nat_ladder_c01934 n (by omega) (by omega)
            · -- n <= 1058246008531
              exact RamareSaouter2003.prime_interval_nat_ladder_c01933 n (by omega) (by omega)
          · -- n <= 1055561684963
            exact RamareSaouter2003.prime_interval_nat_ladder_c01932 n (by omega) (by omega)
      · -- n <= 1052884133363
        rcases Nat.lt_or_ge 1044891940997 n with h8 | h8
        · -- n > 1044891940997
          rcases Nat.lt_or_ge 1047549278341 n with h10 | h10
          · -- n > 1047549278341
            rcases Nat.lt_or_ge 1050213336847 n with h12 | h12
            · -- n > 1050213336847
              exact RamareSaouter2003.prime_interval_nat_ladder_c01931 n (by omega) (by omega)
            · -- n <= 1050213336847
              exact RamareSaouter2003.prime_interval_nat_ladder_c01930 n (by omega) (by omega)
          · -- n <= 1047549278341
            exact RamareSaouter2003.prime_interval_nat_ladder_c01929 n (by omega) (by omega)
        · -- n <= 1044891940997
          rcases Nat.lt_or_ge 1039597362049 n with h10 | h10
          · -- n > 1039597362049
            rcases Nat.lt_or_ge 1042241307781 n with h12 | h12
            · -- n > 1042241307781
              exact RamareSaouter2003.prime_interval_nat_ladder_c01928 n (by omega) (by omega)
            · -- n <= 1042241307781
              exact RamareSaouter2003.prime_interval_nat_ladder_c01927 n (by omega) (by omega)
          · -- n <= 1039597362049
            exact RamareSaouter2003.prime_interval_nat_ladder_c01926 n (by omega) (by omega)
  · -- n <= 1036960086947
    rcases Nat.lt_or_ge 1003274982103 n with h4 | h4
    · -- n > 1003274982103
      rcases Nat.lt_or_ge 1018684539317 n with h6 | h6
      · -- n > 1018684539317
        rcases Nat.lt_or_ge 1026477359009 n with h8 | h8
        · -- n > 1026477359009
          rcases Nat.lt_or_ge 1031705481853 n with h10 | h10
          · -- n > 1031705481853
            rcases Nat.lt_or_ge 1034329465781 n with h12 | h12
            · -- n > 1034329465781
              exact RamareSaouter2003.prime_interval_nat_ladder_c01925 n (by omega) (by omega)
            · -- n <= 1034329465781
              exact RamareSaouter2003.prime_interval_nat_ladder_c01924 n (by omega) (by omega)
          · -- n <= 1031705481853
            rcases Nat.lt_or_ge 1029088118459 n with h12 | h12
            · -- n > 1029088118459
              exact RamareSaouter2003.prime_interval_nat_ladder_c01923 n (by omega) (by omega)
            · -- n <= 1029088118459
              exact RamareSaouter2003.prime_interval_nat_ladder_c01922 n (by omega) (by omega)
        · -- n <= 1026477359009
          rcases Nat.lt_or_ge 1021275586063 n with h10 | h10
          · -- n > 1021275586063
            rcases Nat.lt_or_ge 1023873187111 n with h12 | h12
            · -- n > 1023873187111
              exact RamareSaouter2003.prime_interval_nat_ladder_c01921 n (by omega) (by omega)
            · -- n <= 1023873187111
              exact RamareSaouter2003.prime_interval_nat_ladder_c01920 n (by omega) (by omega)
          · -- n <= 1021275586063
            exact RamareSaouter2003.prime_interval_nat_ladder_c01919 n (by omega) (by omega)
      · -- n <= 1018684539317
        rcases Nat.lt_or_ge 1010950560911 n with h8 | h8
        · -- n > 1010950560911
          rcases Nat.lt_or_ge 1013522043137 n with h10 | h10
          · -- n > 1013522043137
            rcases Nat.lt_or_ge 1016100030443 n with h12 | h12
            · -- n > 1016100030443
              exact RamareSaouter2003.prime_interval_nat_ladder_c01918 n (by omega) (by omega)
            · -- n <= 1016100030443
              exact RamareSaouter2003.prime_interval_nat_ladder_c01917 n (by omega) (by omega)
          · -- n <= 1013522043137
            exact RamareSaouter2003.prime_interval_nat_ladder_c01916 n (by omega) (by omega)
        · -- n <= 1010950560911
          rcases Nat.lt_or_ge 1005827046677 n with h10 | h10
          · -- n > 1005827046677
            rcases Nat.lt_or_ge 1008385567529 n with h12 | h12
            · -- n > 1008385567529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01915 n (by omega) (by omega)
            · -- n <= 1008385567529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01914 n (by omega) (by omega)
          · -- n <= 1005827046677
            exact RamareSaouter2003.prime_interval_nat_ladder_c01913 n (by omega) (by omega)
    · -- n <= 1003274982103
      rcases Nat.lt_or_ge 988098536569 n with h6 | h6
      · -- n > 988098536569
        rcases Nat.lt_or_ge 995657592299 n with h8 | h8
        · -- n > 995657592299
          rcases Nat.lt_or_ge 998190224281 n with h10 | h10
          · -- n > 998190224281
            rcases Nat.lt_or_ge 1000729357627 n with h12 | h12
            · -- n > 1000729357627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01912 n (by omega) (by omega)
            · -- n <= 1000729357627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01911 n (by omega) (by omega)
          · -- n <= 998190224281
            exact RamareSaouter2003.prime_interval_nat_ladder_c01910 n (by omega) (by omega)
        · -- n <= 995657592299
          rcases Nat.lt_or_ge 990611765021 n with h10 | h10
          · -- n > 990611765021
            rcases Nat.lt_or_ge 993131444771 n with h12 | h12
            · -- n > 993131444771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01909 n (by omega) (by omega)
            · -- n <= 993131444771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01908 n (by omega) (by omega)
          · -- n <= 990611765021
            exact RamareSaouter2003.prime_interval_nat_ladder_c01907 n (by omega) (by omega)
      · -- n <= 988098536569
        rcases Nat.lt_or_ge 980597390797 n with h8 | h8
        · -- n > 980597390797
          rcases Nat.lt_or_ge 983091366013 n with h10 | h10
          · -- n > 983091366013
            rcases Nat.lt_or_ge 985591742389 n with h12 | h12
            · -- n > 985591742389
              exact RamareSaouter2003.prime_interval_nat_ladder_c01906 n (by omega) (by omega)
            · -- n <= 985591742389
              exact RamareSaouter2003.prime_interval_nat_ladder_c01905 n (by omega) (by omega)
          · -- n <= 983091366013
            exact RamareSaouter2003.prime_interval_nat_ladder_c01904 n (by omega) (by omega)
        · -- n <= 980597390797
          rcases Nat.lt_or_ge 975628578019 n with h10 | h10
          · -- n > 975628578019
            rcases Nat.lt_or_ge 978109800347 n with h12 | h12
            · -- n > 978109800347
              exact RamareSaouter2003.prime_interval_nat_ladder_c01903 n (by omega) (by omega)
            · -- n <= 978109800347
              exact RamareSaouter2003.prime_interval_nat_ladder_c01902 n (by omega) (by omega)
          · -- n <= 975628578019
            exact RamareSaouter2003.prime_interval_nat_ladder_c01901 n (by omega) (by omega)
