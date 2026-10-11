-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T01:49:06.471112+00:00
-- url     : https://prove2.me/submissions/9ccf897c-5159-4d74-8135-82d507ff2325

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01000

theorem solution (n : Nat)
    (hn : 90188138827 < n) (hupper : n <= 101332544893) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 95553572617 n with h2 | h2
  · -- n > 95553572617
    rcases Nat.lt_or_ge 98243817407 n with h4 | h4
    · -- n > 98243817407
      rcases Nat.lt_or_ge 99617853113 n with h6 | h6
      · -- n > 99617853113
        rcases Nat.lt_or_ge 100329427343 n with h8 | h8
        · -- n > 100329427343
          rcases Nat.lt_or_ge 100829727013 n with h10 | h10
          · -- n > 100829727013
            rcases Nat.lt_or_ge 101080820389 n with h12 | h12
            · -- n > 101080820389
              exact RamareSaouter2003.prime_interval_nat_ladder_c01000 n (by omega) (by omega)
            · -- n <= 101080820389
              exact RamareSaouter2003.prime_interval_nat_ladder_c00999 n (by omega) (by omega)
          · -- n <= 100829727013
            rcases Nat.lt_or_ge 100579263193 n with h12 | h12
            · -- n > 100579263193
              exact RamareSaouter2003.prime_interval_nat_ladder_c00998 n (by omega) (by omega)
            · -- n <= 100579263193
              exact RamareSaouter2003.prime_interval_nat_ladder_c00997 n (by omega) (by omega)
        · -- n <= 100329427343
          rcases Nat.lt_or_ge 99848761897 n with h10 | h10
          · -- n > 99848761897
            rcases Nat.lt_or_ge 100080217907 n with h12 | h12
            · -- n > 100080217907
              exact RamareSaouter2003.prime_interval_nat_ladder_c00996 n (by omega) (by omega)
            · -- n <= 100080217907
              exact RamareSaouter2003.prime_interval_nat_ladder_c00995 n (by omega) (by omega)
          · -- n <= 99848761897
            exact RamareSaouter2003.prime_interval_nat_ladder_c00994 n (by omega) (by omega)
      · -- n <= 99617853113
        rcases Nat.lt_or_ge 98928396583 n with h8 | h8
        · -- n > 98928396583
          rcases Nat.lt_or_ge 99157671779 n with h10 | h10
          · -- n > 99157671779
            rcases Nat.lt_or_ge 99387490193 n with h12 | h12
            · -- n > 99387490193
              exact RamareSaouter2003.prime_interval_nat_ladder_c00993 n (by omega) (by omega)
            · -- n <= 99387490193
              exact RamareSaouter2003.prime_interval_nat_ladder_c00992 n (by omega) (by omega)
          · -- n <= 99157671779
            exact RamareSaouter2003.prime_interval_nat_ladder_c00991 n (by omega) (by omega)
        · -- n <= 98928396583
          rcases Nat.lt_or_ge 98471470771 n with h10 | h10
          · -- n > 98471470771
            rcases Nat.lt_or_ge 98699663423 n with h12 | h12
            · -- n > 98699663423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00990 n (by omega) (by omega)
            · -- n <= 98699663423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00989 n (by omega) (by omega)
          · -- n <= 98471470771
            exact RamareSaouter2003.prime_interval_nat_ladder_c00988 n (by omega) (by omega)
    · -- n <= 98243817407
      rcases Nat.lt_or_ge 96889150247 n with h6 | h6
      · -- n > 96889150247
        rcases Nat.lt_or_ge 97564080281 n with h8 | h8
        · -- n > 97564080281
          rcases Nat.lt_or_ge 97790123531 n with h10 | h10
          · -- n > 97790123531
            rcases Nat.lt_or_ge 98016702083 n with h12 | h12
            · -- n > 98016702083
              exact RamareSaouter2003.prime_interval_nat_ladder_c00987 n (by omega) (by omega)
            · -- n <= 98016702083
              exact RamareSaouter2003.prime_interval_nat_ladder_c00986 n (by omega) (by omega)
          · -- n <= 97790123531
            exact RamareSaouter2003.prime_interval_nat_ladder_c00985 n (by omega) (by omega)
        · -- n <= 97564080281
          rcases Nat.lt_or_ge 97113594997 n with h10 | h10
          · -- n > 97113594997
            rcases Nat.lt_or_ge 97338571181 n with h12 | h12
            · -- n > 97338571181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00984 n (by omega) (by omega)
            · -- n <= 97338571181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00983 n (by omega) (by omega)
          · -- n <= 97113594997
            exact RamareSaouter2003.prime_interval_nat_ladder_c00982 n (by omega) (by omega)
      · -- n <= 96889150247
        rcases Nat.lt_or_ge 96218992501 n with h8 | h8
        · -- n > 96218992501
          rcases Nat.lt_or_ge 96441850313 n with h10 | h10
          · -- n > 96441850313
            rcases Nat.lt_or_ge 96665235781 n with h12 | h12
            · -- n > 96665235781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00981 n (by omega) (by omega)
            · -- n <= 96665235781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00980 n (by omega) (by omega)
          · -- n <= 96441850313
            exact RamareSaouter2003.prime_interval_nat_ladder_c00979 n (by omega) (by omega)
        · -- n <= 96218992501
          rcases Nat.lt_or_ge 95774854939 n with h10 | h10
          · -- n > 95774854939
            rcases Nat.lt_or_ge 95996661151 n with h12 | h12
            · -- n > 95996661151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00978 n (by omega) (by omega)
            · -- n <= 95996661151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00977 n (by omega) (by omega)
          · -- n <= 95774854939
            exact RamareSaouter2003.prime_interval_nat_ladder_c00976 n (by omega) (by omega)
  · -- n <= 95553572617
    rcases Nat.lt_or_ge 92724006527 n with h4 | h4
    · -- n > 92724006527
      rcases Nat.lt_or_ge 94019159951 n with h6 | h6
      · -- n > 94019159951
        rcases Nat.lt_or_ge 94673657081 n with h8 | h8
        · -- n > 94673657081
          rcases Nat.lt_or_ge 95112574633 n with h10 | h10
          · -- n > 95112574633
            rcases Nat.lt_or_ge 95332812931 n with h12 | h12
            · -- n > 95332812931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00975 n (by omega) (by omega)
            · -- n <= 95332812931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00974 n (by omega) (by omega)
          · -- n <= 95112574633
            rcases Nat.lt_or_ge 94892856431 n with h12 | h12
            · -- n > 94892856431
              exact RamareSaouter2003.prime_interval_nat_ladder_c00973 n (by omega) (by omega)
            · -- n <= 94892856431
              exact RamareSaouter2003.prime_interval_nat_ladder_c00972 n (by omega) (by omega)
        · -- n <= 94673657081
          rcases Nat.lt_or_ge 94236810167 n with h10 | h10
          · -- n > 94236810167
            rcases Nat.lt_or_ge 94454975431 n with h12 | h12
            · -- n > 94454975431
              exact RamareSaouter2003.prime_interval_nat_ladder_c00971 n (by omega) (by omega)
            · -- n <= 94454975431
              exact RamareSaouter2003.prime_interval_nat_ladder_c00970 n (by omega) (by omega)
          · -- n <= 94236810167
            exact RamareSaouter2003.prime_interval_nat_ladder_c00969 n (by omega) (by omega)
      · -- n <= 94019159951
        rcases Nat.lt_or_ge 93369287507 n with h8 | h8
        · -- n > 93369287507
          rcases Nat.lt_or_ge 93585399811 n with h10 | h10
          · -- n > 93585399811
            rcases Nat.lt_or_ge 93802023577 n with h12 | h12
            · -- n > 93802023577
              exact RamareSaouter2003.prime_interval_nat_ladder_c00968 n (by omega) (by omega)
            · -- n <= 93802023577
              exact RamareSaouter2003.prime_interval_nat_ladder_c00967 n (by omega) (by omega)
          · -- n <= 93585399811
            exact RamareSaouter2003.prime_interval_nat_ladder_c00966 n (by omega) (by omega)
        · -- n <= 93369287507
          rcases Nat.lt_or_ge 92938592081 n with h10 | h10
          · -- n > 92938592081
            rcases Nat.lt_or_ge 93153685307 n with h12 | h12
            · -- n > 93153685307
              exact RamareSaouter2003.prime_interval_nat_ladder_c00965 n (by omega) (by omega)
            · -- n <= 93153685307
              exact RamareSaouter2003.prime_interval_nat_ladder_c00964 n (by omega) (by omega)
          · -- n <= 92938592081
            exact RamareSaouter2003.prime_interval_nat_ladder_c00963 n (by omega) (by omega)
    · -- n <= 92724006527
      rcases Nat.lt_or_ge 91447086931 n with h6 | h6
      · -- n > 91447086931
        rcases Nat.lt_or_ge 92083283909 n with h8 | h8
        · -- n > 92083283909
          rcases Nat.lt_or_ge 92296353673 n with h10 | h10
          · -- n > 92296353673
            rcases Nat.lt_or_ge 92509927453 n with h12 | h12
            · -- n > 92509927453
              exact RamareSaouter2003.prime_interval_nat_ladder_c00962 n (by omega) (by omega)
            · -- n <= 92509927453
              exact RamareSaouter2003.prime_interval_nat_ladder_c00961 n (by omega) (by omega)
          · -- n <= 92296353673
            exact RamareSaouter2003.prime_interval_nat_ladder_c00960 n (by omega) (by omega)
        · -- n <= 92083283909
          rcases Nat.lt_or_ge 91658651837 n with h10 | h10
          · -- n > 91658651837
            rcases Nat.lt_or_ge 91870717019 n with h12 | h12
            · -- n > 91870717019
              exact RamareSaouter2003.prime_interval_nat_ladder_c00959 n (by omega) (by omega)
            · -- n <= 91870717019
              exact RamareSaouter2003.prime_interval_nat_ladder_c00958 n (by omega) (by omega)
          · -- n <= 91658651837
            exact RamareSaouter2003.prime_interval_nat_ladder_c00957 n (by omega) (by omega)
      · -- n <= 91447086931
        rcases Nat.lt_or_ge 90815382611 n with h8 | h8
        · -- n > 90815382611
          rcases Nat.lt_or_ge 91025453509 n with h10 | h10
          · -- n > 91025453509
            rcases Nat.lt_or_ge 91236021221 n with h12 | h12
            · -- n > 91236021221
              exact RamareSaouter2003.prime_interval_nat_ladder_c00956 n (by omega) (by omega)
            · -- n <= 91236021221
              exact RamareSaouter2003.prime_interval_nat_ladder_c00955 n (by omega) (by omega)
          · -- n <= 91025453509
            exact RamareSaouter2003.prime_interval_nat_ladder_c00954 n (by omega) (by omega)
        · -- n <= 90815382611
          rcases Nat.lt_or_ge 90396726523 n with h10 | h10
          · -- n > 90396726523
            rcases Nat.lt_or_ge 90605807401 n with h12 | h12
            · -- n > 90605807401
              exact RamareSaouter2003.prime_interval_nat_ladder_c00953 n (by omega) (by omega)
            · -- n <= 90605807401
              exact RamareSaouter2003.prime_interval_nat_ladder_c00952 n (by omega) (by omega)
          · -- n <= 90396726523
            exact RamareSaouter2003.prime_interval_nat_ladder_c00951 n (by omega) (by omega)
