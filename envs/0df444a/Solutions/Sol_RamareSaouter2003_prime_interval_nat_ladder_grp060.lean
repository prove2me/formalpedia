-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T01:23:21.244241+00:00
-- url     : https://prove2.me/submissions/c518fd50-ba1a-4dba-9258-72c20189afa6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03000

theorem solution (n : Nat)
    (hn : 13410251849639 < n) (hupper : n <= 15174303375743) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 14265035222521 n with h2 | h2
  · -- n > 14265035222521
    rcases Nat.lt_or_ge 14694475433749 n with h4 | h4
    · -- n > 14694475433749
      rcases Nat.lt_or_ge 14914019499209 n with h6 | h6
      · -- n > 14914019499209
        rcases Nat.lt_or_ge 15025018529789 n with h8 | h8
        · -- n > 15025018529789
          rcases Nat.lt_or_ge 15099476461021 n with h10 | h10
          · -- n > 15099476461021
            rcases Nat.lt_or_ge 15136843681411 n with h12 | h12
            · -- n > 15136843681411
              exact RamareSaouter2003.prime_interval_nat_ladder_c03000 n (by omega) (by omega)
            · -- n <= 15136843681411
              exact RamareSaouter2003.prime_interval_nat_ladder_c02999 n (by omega) (by omega)
          · -- n <= 15099476461021
            rcases Nat.lt_or_ge 15062201486351 n with h12 | h12
            · -- n > 15062201486351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02998 n (by omega) (by omega)
            · -- n <= 15062201486351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02997 n (by omega) (by omega)
        · -- n <= 15025018529789
          rcases Nat.lt_or_ge 14950927762567 n with h10 | h10
          · -- n > 14950927762567
            rcases Nat.lt_or_ge 14987927364083 n with h12 | h12
            · -- n > 14987927364083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02996 n (by omega) (by omega)
            · -- n <= 14987927364083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02995 n (by omega) (by omega)
          · -- n <= 14950927762567
            exact RamareSaouter2003.prime_interval_nat_ladder_c02994 n (by omega) (by omega)
      · -- n <= 14914019499209
        rcases Nat.lt_or_ge 14803840486597 n with h8 | h8
        · -- n > 14803840486597
          rcases Nat.lt_or_ge 14840476085977 n with h10 | h10
          · -- n > 14840476085977
            rcases Nat.lt_or_ge 14877202348751 n with h12 | h12
            · -- n > 14877202348751
              exact RamareSaouter2003.prime_interval_nat_ladder_c02993 n (by omega) (by omega)
            · -- n <= 14877202348751
              exact RamareSaouter2003.prime_interval_nat_ladder_c02992 n (by omega) (by omega)
          · -- n <= 14840476085977
            exact RamareSaouter2003.prime_interval_nat_ladder_c02991 n (by omega) (by omega)
        · -- n <= 14803840486597
          rcases Nat.lt_or_ge 14730840383473 n with h10 | h10
          · -- n > 14730840383473
            rcases Nat.lt_or_ge 14767295326853 n with h12 | h12
            · -- n > 14767295326853
              exact RamareSaouter2003.prime_interval_nat_ladder_c02990 n (by omega) (by omega)
            · -- n <= 14767295326853
              exact RamareSaouter2003.prime_interval_nat_ladder_c02989 n (by omega) (by omega)
          · -- n <= 14730840383473
            exact RamareSaouter2003.prime_interval_nat_ladder_c02988 n (by omega) (by omega)
    · -- n <= 14694475433749
      rcases Nat.lt_or_ge 14478163199729 n with h6 | h6
      · -- n > 14478163199729
        rcases Nat.lt_or_ge 14585918327683 n with h8 | h8
        · -- n > 14585918327683
          rcases Nat.lt_or_ge 14622014627201 n with h10 | h10
          · -- n > 14622014627201
            rcases Nat.lt_or_ge 14658200255519 n with h12 | h12
            · -- n > 14658200255519
              exact RamareSaouter2003.prime_interval_nat_ladder_c02987 n (by omega) (by omega)
            · -- n <= 14658200255519
              exact RamareSaouter2003.prime_interval_nat_ladder_c02986 n (by omega) (by omega)
          · -- n <= 14622014627201
            exact RamareSaouter2003.prime_interval_nat_ladder_c02985 n (by omega) (by omega)
        · -- n <= 14585918327683
          rcases Nat.lt_or_ge 14513992833707 n with h10 | h10
          · -- n > 14513992833707
            rcases Nat.lt_or_ge 14549911136569 n with h12 | h12
            · -- n > 14549911136569
              exact RamareSaouter2003.prime_interval_nat_ladder_c02984 n (by omega) (by omega)
            · -- n <= 14549911136569
              exact RamareSaouter2003.prime_interval_nat_ladder_c02983 n (by omega) (by omega)
          · -- n <= 14513992833707
            exact RamareSaouter2003.prime_interval_nat_ladder_c02982 n (by omega) (by omega)
      · -- n <= 14478163199729
        rcases Nat.lt_or_ge 14371204124923 n with h8 | h8
        · -- n > 14371204124923
          rcases Nat.lt_or_ge 14406769063429 n with h10 | h10
          · -- n > 14406769063429
            rcases Nat.lt_or_ge 14442422015729 n with h12 | h12
            · -- n > 14442422015729
              exact RamareSaouter2003.prime_interval_nat_ladder_c02981 n (by omega) (by omega)
            · -- n <= 14442422015729
              exact RamareSaouter2003.prime_interval_nat_ladder_c02980 n (by omega) (by omega)
          · -- n <= 14406769063429
            exact RamareSaouter2003.prime_interval_nat_ladder_c02979 n (by omega) (by omega)
        · -- n <= 14371204124923
          rcases Nat.lt_or_ge 14300337420893 n with h10 | h10
          · -- n > 14300337420893
            rcases Nat.lt_or_ge 14335726982963 n with h12 | h12
            · -- n > 14335726982963
              exact RamareSaouter2003.prime_interval_nat_ladder_c02978 n (by omega) (by omega)
            · -- n <= 14335726982963
              exact RamareSaouter2003.prime_interval_nat_ladder_c02977 n (by omega) (by omega)
          · -- n <= 14300337420893
            exact RamareSaouter2003.prime_interval_nat_ladder_c02976 n (by omega) (by omega)
  · -- n <= 14265035222521
    rcases Nat.lt_or_ge 13813959326861 n with h4 | h4
    · -- n > 13813959326861
      rcases Nat.lt_or_ge 14020347965989 n with h6 | h6
      · -- n > 14020347965989
        rcases Nat.lt_or_ge 14124695759621 n with h8 | h8
        · -- n > 14124695759621
          rcases Nat.lt_or_ge 14194692054317 n with h10 | h10
          · -- n > 14194692054317
            rcases Nat.lt_or_ge 14229820172017 n with h12 | h12
            · -- n > 14229820172017
              exact RamareSaouter2003.prime_interval_nat_ladder_c02975 n (by omega) (by omega)
            · -- n <= 14229820172017
              exact RamareSaouter2003.prime_interval_nat_ladder_c02974 n (by omega) (by omega)
          · -- n <= 14194692054317
            rcases Nat.lt_or_ge 14159650654883 n with h12 | h12
            · -- n > 14159650654883
              exact RamareSaouter2003.prime_interval_nat_ladder_c02973 n (by omega) (by omega)
            · -- n <= 14159650654883
              exact RamareSaouter2003.prime_interval_nat_ladder_c02972 n (by omega) (by omega)
        · -- n <= 14124695759621
          rcases Nat.lt_or_ge 14055044627861 n with h10 | h10
          · -- n > 14055044627861
            rcases Nat.lt_or_ge 14089827154861 n with h12 | h12
            · -- n > 14089827154861
              exact RamareSaouter2003.prime_interval_nat_ladder_c02971 n (by omega) (by omega)
            · -- n <= 14089827154861
              exact RamareSaouter2003.prime_interval_nat_ladder_c02970 n (by omega) (by omega)
          · -- n <= 14055044627861
            exact RamareSaouter2003.prime_interval_nat_ladder_c02969 n (by omega) (by omega)
      · -- n <= 14020347965989
        rcases Nat.lt_or_ge 13916771053373 n with h8 | h8
        · -- n > 13916771053373
          rcases Nat.lt_or_ge 13951211389933 n with h10 | h10
          · -- n > 13951211389933
            rcases Nat.lt_or_ge 13985736957061 n with h12 | h12
            · -- n > 13985736957061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02968 n (by omega) (by omega)
            · -- n <= 13985736957061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02967 n (by omega) (by omega)
          · -- n <= 13951211389933
            exact RamareSaouter2003.prime_interval_nat_ladder_c02966 n (by omega) (by omega)
        · -- n <= 13916771053373
          rcases Nat.lt_or_ge 13848145231483 n with h10 | h10
          · -- n > 13848145231483
            rcases Nat.lt_or_ge 13882415737139 n with h12 | h12
            · -- n > 13882415737139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02965 n (by omega) (by omega)
            · -- n <= 13882415737139
              exact RamareSaouter2003.prime_interval_nat_ladder_c02964 n (by omega) (by omega)
          · -- n <= 13848145231483
            exact RamareSaouter2003.prime_interval_nat_ladder_c02963 n (by omega) (by omega)
    · -- n <= 13813959326861
      rcases Nat.lt_or_ge 13610608862819 n with h6 | h6
      · -- n > 13610608862819
        rcases Nat.lt_or_ge 13711907133761 n with h8 | h8
        · -- n > 13711907133761
          rcases Nat.lt_or_ge 13745840486129 n with h10 | h10
          · -- n > 13745840486129
            rcases Nat.lt_or_ge 13779857814451 n with h12 | h12
            · -- n > 13779857814451
              exact RamareSaouter2003.prime_interval_nat_ladder_c02962 n (by omega) (by omega)
            · -- n <= 13779857814451
              exact RamareSaouter2003.prime_interval_nat_ladder_c02961 n (by omega) (by omega)
          · -- n <= 13745840486129
            exact RamareSaouter2003.prime_interval_nat_ladder_c02960 n (by omega) (by omega)
        · -- n <= 13711907133761
          rcases Nat.lt_or_ge 13644291528667 n with h10 | h10
          · -- n > 13644291528667
            rcases Nat.lt_or_ge 13678057550123 n with h12 | h12
            · -- n > 13678057550123
              exact RamareSaouter2003.prime_interval_nat_ladder_c02959 n (by omega) (by omega)
            · -- n <= 13678057550123
              exact RamareSaouter2003.prime_interval_nat_ladder_c02958 n (by omega) (by omega)
          · -- n <= 13644291528667
            exact RamareSaouter2003.prime_interval_nat_ladder_c02957 n (by omega) (by omega)
      · -- n <= 13610608862819
        rcases Nat.lt_or_ge 13510058944303 n with h8 | h8
        · -- n > 13510058944303
          rcases Nat.lt_or_ge 13543492775663 n with h10 | h10
          · -- n > 13543492775663
            rcases Nat.lt_or_ge 13577009346949 n with h12 | h12
            · -- n > 13577009346949
              exact RamareSaouter2003.prime_interval_nat_ladder_c02956 n (by omega) (by omega)
            · -- n <= 13577009346949
              exact RamareSaouter2003.prime_interval_nat_ladder_c02955 n (by omega) (by omega)
          · -- n <= 13543492775663
            exact RamareSaouter2003.prime_interval_nat_ladder_c02954 n (by omega) (by omega)
        · -- n <= 13510058944303
          rcases Nat.lt_or_ge 13443438684811 n with h10 | h10
          · -- n > 13443438684811
            rcases Nat.lt_or_ge 13476707648557 n with h12 | h12
            · -- n > 13476707648557
              exact RamareSaouter2003.prime_interval_nat_ladder_c02953 n (by omega) (by omega)
            · -- n <= 13476707648557
              exact RamareSaouter2003.prime_interval_nat_ladder_c02952 n (by omega) (by omega)
          · -- n <= 13443438684811
            exact RamareSaouter2003.prime_interval_nat_ladder_c02951 n (by omega) (by omega)
