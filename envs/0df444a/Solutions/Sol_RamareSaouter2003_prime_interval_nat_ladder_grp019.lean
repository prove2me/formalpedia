-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T01:17:59.814984+00:00
-- url     : https://prove2.me/submissions/4de6f7be-f48d-4787-83c0-b797f9cf665c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00950

theorem solution (n : Nat)
    (hn : 80362118567 < n) (hupper : n <= 90188138827) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 85130317549 n with h2 | h2
  · -- n > 85130317549
    rcases Nat.lt_or_ge 87520845109 n with h4 | h4
    · -- n > 87520845109
      rcases Nat.lt_or_ge 88741735783 n with h6 | h6
      · -- n > 88741735783
        rcases Nat.lt_or_ge 89358696613 n with h8 | h8
        · -- n > 89358696613
          rcases Nat.lt_or_ge 89772438361 n with h10 | h10
          · -- n > 89772438361
            rcases Nat.lt_or_ge 89980043171 n with h12 | h12
            · -- n > 89980043171
              exact RamareSaouter2003.prime_interval_nat_ladder_c00950 n (by omega) (by omega)
            · -- n <= 89980043171
              exact RamareSaouter2003.prime_interval_nat_ladder_c00949 n (by omega) (by omega)
          · -- n <= 89772438361
            rcases Nat.lt_or_ge 89565323219 n with h12 | h12
            · -- n > 89565323219
              exact RamareSaouter2003.prime_interval_nat_ladder_c00948 n (by omega) (by omega)
            · -- n <= 89565323219
              exact RamareSaouter2003.prime_interval_nat_ladder_c00947 n (by omega) (by omega)
        · -- n <= 89358696613
          rcases Nat.lt_or_ge 88946904049 n with h10 | h10
          · -- n > 88946904049
            rcases Nat.lt_or_ge 89152557253 n with h12 | h12
            · -- n > 89152557253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00946 n (by omega) (by omega)
            · -- n <= 89152557253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00945 n (by omega) (by omega)
          · -- n <= 88946904049
            exact RamareSaouter2003.prime_interval_nat_ladder_c00944 n (by omega) (by omega)
      · -- n <= 88741735783
        rcases Nat.lt_or_ge 88129129079 n with h8 | h8
        · -- n > 88129129079
          rcases Nat.lt_or_ge 88332849469 n with h10 | h10
          · -- n > 88332849469
            rcases Nat.lt_or_ge 88537051327 n with h12 | h12
            · -- n > 88537051327
              exact RamareSaouter2003.prime_interval_nat_ladder_c00943 n (by omega) (by omega)
            · -- n <= 88537051327
              exact RamareSaouter2003.prime_interval_nat_ladder_c00942 n (by omega) (by omega)
          · -- n <= 88332849469
            exact RamareSaouter2003.prime_interval_nat_ladder_c00941 n (by omega) (by omega)
        · -- n <= 88129129079
          rcases Nat.lt_or_ge 87723128047 n with h10 | h10
          · -- n > 87723128047
            rcases Nat.lt_or_ge 87925888987 n with h12 | h12
            · -- n > 87925888987
              exact RamareSaouter2003.prime_interval_nat_ladder_c00940 n (by omega) (by omega)
            · -- n <= 87925888987
              exact RamareSaouter2003.prime_interval_nat_ladder_c00939 n (by omega) (by omega)
          · -- n <= 87723128047
            exact RamareSaouter2003.prime_interval_nat_ladder_c00938 n (by omega) (by omega)
    · -- n <= 87520845109
      rcases Nat.lt_or_ge 86317121197 n with h6 | h6
      · -- n > 86317121197
        rcases Nat.lt_or_ge 86916852791 n with h8 | h8
        · -- n > 86916852791
          rcases Nat.lt_or_ge 87117708619 n with h10 | h10
          · -- n > 87117708619
            rcases Nat.lt_or_ge 87319039007 n with h12 | h12
            · -- n > 87319039007
              exact RamareSaouter2003.prime_interval_nat_ladder_c00937 n (by omega) (by omega)
            · -- n <= 87319039007
              exact RamareSaouter2003.prime_interval_nat_ladder_c00936 n (by omega) (by omega)
          · -- n <= 87117708619
            exact RamareSaouter2003.prime_interval_nat_ladder_c00935 n (by omega) (by omega)
        · -- n <= 86916852791
          rcases Nat.lt_or_ge 86516560213 n with h10 | h10
          · -- n > 86516560213
            rcases Nat.lt_or_ge 86716470397 n with h12 | h12
            · -- n > 86716470397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00934 n (by omega) (by omega)
            · -- n <= 86716470397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00933 n (by omega) (by omega)
          · -- n <= 86516560213
            exact RamareSaouter2003.prime_interval_nat_ladder_c00932 n (by omega) (by omega)
      · -- n <= 86317121197
        rcases Nat.lt_or_ge 85721619637 n with h8 | h8
        · -- n > 85721619637
          rcases Nat.lt_or_ge 85919652019 n with h10 | h10
          · -- n > 85919652019
            rcases Nat.lt_or_ge 86118152149 n with h12 | h12
            · -- n > 86118152149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00931 n (by omega) (by omega)
            · -- n <= 86118152149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00930 n (by omega) (by omega)
          · -- n <= 85919652019
            exact RamareSaouter2003.prime_interval_nat_ladder_c00929 n (by omega) (by omega)
        · -- n <= 85721619637
          rcases Nat.lt_or_ge 85326953477 n with h10 | h10
          · -- n > 85326953477
            rcases Nat.lt_or_ge 85524053801 n with h12 | h12
            · -- n > 85524053801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00928 n (by omega) (by omega)
            · -- n <= 85524053801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00927 n (by omega) (by omega)
          · -- n <= 85326953477
            exact RamareSaouter2003.prime_interval_nat_ladder_c00926 n (by omega) (by omega)
  · -- n <= 85130317549
    rcases Nat.lt_or_ge 82615803157 n with h4 | h4
    · -- n > 82615803157
      rcases Nat.lt_or_ge 83766774677 n with h6 | h6
      · -- n > 83766774677
        rcases Nat.lt_or_ge 84348395099 n with h8 | h8
        · -- n > 84348395099
          rcases Nat.lt_or_ge 84738434281 n with h10 | h10
          · -- n > 84738434281
            rcases Nat.lt_or_ge 84934144837 n with h12 | h12
            · -- n > 84934144837
              exact RamareSaouter2003.prime_interval_nat_ladder_c00925 n (by omega) (by omega)
            · -- n <= 84934144837
              exact RamareSaouter2003.prime_interval_nat_ladder_c00924 n (by omega) (by omega)
          · -- n <= 84738434281
            rcases Nat.lt_or_ge 84543184723 n with h12 | h12
            · -- n > 84543184723
              exact RamareSaouter2003.prime_interval_nat_ladder_c00923 n (by omega) (by omega)
            · -- n <= 84543184723
              exact RamareSaouter2003.prime_interval_nat_ladder_c00922 n (by omega) (by omega)
        · -- n <= 84348395099
          rcases Nat.lt_or_ge 83960191171 n with h10 | h10
          · -- n > 83960191171
            rcases Nat.lt_or_ge 84154064299 n with h12 | h12
            · -- n > 84154064299
              exact RamareSaouter2003.prime_interval_nat_ladder_c00921 n (by omega) (by omega)
            · -- n <= 84154064299
              exact RamareSaouter2003.prime_interval_nat_ladder_c00920 n (by omega) (by omega)
          · -- n <= 83960191171
            exact RamareSaouter2003.prime_interval_nat_ladder_c00919 n (by omega) (by omega)
      · -- n <= 83766774677
        rcases Nat.lt_or_ge 83189253871 n with h8 | h8
        · -- n > 83189253871
          rcases Nat.lt_or_ge 83381307103 n with h10 | h10
          · -- n > 83381307103
            rcases Nat.lt_or_ge 83573813707 n with h12 | h12
            · -- n > 83573813707
              exact RamareSaouter2003.prime_interval_nat_ladder_c00918 n (by omega) (by omega)
            · -- n <= 83573813707
              exact RamareSaouter2003.prime_interval_nat_ladder_c00917 n (by omega) (by omega)
          · -- n <= 83381307103
            exact RamareSaouter2003.prime_interval_nat_ladder_c00916 n (by omega) (by omega)
        · -- n <= 83189253871
          rcases Nat.lt_or_ge 82806503011 n with h10 | h10
          · -- n > 82806503011
            rcases Nat.lt_or_ge 82997652911 n with h12 | h12
            · -- n > 82997652911
              exact RamareSaouter2003.prime_interval_nat_ladder_c00915 n (by omega) (by omega)
            · -- n <= 82997652911
              exact RamareSaouter2003.prime_interval_nat_ladder_c00914 n (by omega) (by omega)
          · -- n <= 82806503011
            exact RamareSaouter2003.prime_interval_nat_ladder_c00913 n (by omega) (by omega)
    · -- n <= 82615803157
      rcases Nat.lt_or_ge 81480995147 n with h6 | h6
      · -- n > 81480995147
        rcases Nat.lt_or_ge 82046393137 n with h8 | h8
        · -- n > 82046393137
          rcases Nat.lt_or_ge 82235749307 n with h10 | h10
          · -- n > 82235749307
            rcases Nat.lt_or_ge 82425552271 n with h12 | h12
            · -- n > 82425552271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00912 n (by omega) (by omega)
            · -- n <= 82425552271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00911 n (by omega) (by omega)
          · -- n <= 82235749307
            exact RamareSaouter2003.prime_interval_nat_ladder_c00910 n (by omega) (by omega)
        · -- n <= 82046393137
          rcases Nat.lt_or_ge 81669017281 n with h10 | h10
          · -- n > 81669017281
            rcases Nat.lt_or_ge 81857482943 n with h12 | h12
            · -- n > 81857482943
              exact RamareSaouter2003.prime_interval_nat_ladder_c00909 n (by omega) (by omega)
            · -- n <= 81857482943
              exact RamareSaouter2003.prime_interval_nat_ladder_c00908 n (by omega) (by omega)
          · -- n <= 81669017281
            exact RamareSaouter2003.prime_interval_nat_ladder_c00907 n (by omega) (by omega)
      · -- n <= 81480995147
        rcases Nat.lt_or_ge 80919579821 n with h8 | h8
        · -- n > 80919579821
          rcases Nat.lt_or_ge 81106277563 n with h10 | h10
          · -- n > 81106277563
            rcases Nat.lt_or_ge 81293415589 n with h12 | h12
            · -- n > 81293415589
              exact RamareSaouter2003.prime_interval_nat_ladder_c00906 n (by omega) (by omega)
            · -- n <= 81293415589
              exact RamareSaouter2003.prime_interval_nat_ladder_c00905 n (by omega) (by omega)
          · -- n <= 81106277563
            exact RamareSaouter2003.prime_interval_nat_ladder_c00904 n (by omega) (by omega)
        · -- n <= 80919579821
          rcases Nat.lt_or_ge 80547501373 n with h10 | h10
          · -- n > 80547501373
            rcases Nat.lt_or_ge 80733321443 n with h12 | h12
            · -- n > 80733321443
              exact RamareSaouter2003.prime_interval_nat_ladder_c00903 n (by omega) (by omega)
            · -- n <= 80733321443
              exact RamareSaouter2003.prime_interval_nat_ladder_c00902 n (by omega) (by omega)
          · -- n <= 80547501373
            exact RamareSaouter2003.prime_interval_nat_ladder_c00901 n (by omega) (by omega)
