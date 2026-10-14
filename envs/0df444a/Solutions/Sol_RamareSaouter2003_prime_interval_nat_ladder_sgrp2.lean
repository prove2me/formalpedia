-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_sgrp2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T10:34:33.450374+00:00
-- url     : https://prove2.me/submissions/16843570-340f-4313-8b59-c17926674e2e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp050
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp088

theorem solution (n : Nat)
    (hn : 2082320379773 < n) (hupper : n <= 570899461905341) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 31852221937607 n with h2 | h2
  · -- n > 31852221937607
    rcases Nat.lt_or_ge 124030886084041 n with h4 | h4
    · -- n > 124030886084041
      rcases Nat.lt_or_ge 244566045604369 n with h6 | h6
      · -- n > 244566045604369
        rcases Nat.lt_or_ge 373647047298709 n with h8 | h8
        · -- n > 373647047298709
          rcases Nat.lt_or_ge 430355186223233 n with h10 | h10
          · -- n > 430355186223233
            rcases Nat.lt_or_ge 495672413417261 n with h12 | h12
            · -- n > 495672413417261
              exact RamareSaouter2003.prime_interval_nat_ladder_grp088 n (by omega) (by omega)
            · -- n <= 495672413417261
              exact RamareSaouter2003.prime_interval_nat_ladder_grp087 n (by omega) (by omega)
          · -- n <= 430355186223233
            exact RamareSaouter2003.prime_interval_nat_ladder_grp086 n (by omega) (by omega)
        · -- n <= 373647047298709
          rcases Nat.lt_or_ge 281681085386551 n with h10 | h10
          · -- n > 281681085386551
            rcases Nat.lt_or_ge 324415616742421 n with h12 | h12
            · -- n > 324415616742421
              exact RamareSaouter2003.prime_interval_nat_ladder_grp085 n (by omega) (by omega)
            · -- n <= 324415616742421
              exact RamareSaouter2003.prime_interval_nat_ladder_grp084 n (by omega) (by omega)
          · -- n <= 281681085386551
            exact RamareSaouter2003.prime_interval_nat_ladder_grp083 n (by omega) (by omega)
      · -- n <= 244566045604369
        rcases Nat.lt_or_ge 160082286934001 n with h8 | h8
        · -- n > 160082286934001
          rcases Nat.lt_or_ge 184372641394199 n with h10 | h10
          · -- n > 184372641394199
            rcases Nat.lt_or_ge 212343815514223 n with h12 | h12
            · -- n > 212343815514223
              exact RamareSaouter2003.prime_interval_nat_ladder_grp082 n (by omega) (by omega)
            · -- n <= 212343815514223
              exact RamareSaouter2003.prime_interval_nat_ladder_grp081 n (by omega) (by omega)
          · -- n <= 184372641394199
            exact RamareSaouter2003.prime_interval_nat_ladder_grp080 n (by omega) (by omega)
        · -- n <= 160082286934001
          rcases Nat.lt_or_ge 140346528528637 n with h10 | h10
          · -- n > 140346528528637
            exact RamareSaouter2003.prime_interval_nat_ladder_grp079 n (by omega) (by omega)
          · -- n <= 140346528528637
            exact RamareSaouter2003.prime_interval_nat_ladder_grp078 n (by omega) (by omega)
    · -- n <= 124030886084041
      rcases Nat.lt_or_ge 59087943554933 n with h6 | h6
      · -- n > 59087943554933
        rcases Nat.lt_or_ge 85608001936621 n with h8 | h8
        · -- n > 85608001936621
          rcases Nat.lt_or_ge 96869306228069 n with h10 | h10
          · -- n > 96869306228069
            rcases Nat.lt_or_ge 109611978750817 n with h12 | h12
            · -- n > 109611978750817
              exact RamareSaouter2003.prime_interval_nat_ladder_grp077 n (by omega) (by omega)
            · -- n <= 109611978750817
              exact RamareSaouter2003.prime_interval_nat_ladder_grp076 n (by omega) (by omega)
          · -- n <= 96869306228069
            exact RamareSaouter2003.prime_interval_nat_ladder_grp075 n (by omega) (by omega)
        · -- n <= 85608001936621
          rcases Nat.lt_or_ge 66860666865847 n with h10 | h10
          · -- n > 66860666865847
            rcases Nat.lt_or_ge 75655853035559 n with h12 | h12
            · -- n > 75655853035559
              exact RamareSaouter2003.prime_interval_nat_ladder_grp074 n (by omega) (by omega)
            · -- n <= 75655853035559
              exact RamareSaouter2003.prime_interval_nat_ladder_grp073 n (by omega) (by omega)
          · -- n <= 66860666865847
            exact RamareSaouter2003.prime_interval_nat_ladder_grp072 n (by omega) (by omega)
      · -- n <= 59087943554933
        rcases Nat.lt_or_ge 40783396349303 n with h8 | h8
        · -- n > 40783396349303
          rcases Nat.lt_or_ge 46148248066457 n with h10 | h10
          · -- n > 46148248066457
            rcases Nat.lt_or_ge 52218819183697 n with h12 | h12
            · -- n > 52218819183697
              exact RamareSaouter2003.prime_interval_nat_ladder_grp071 n (by omega) (by omega)
            · -- n <= 52218819183697
              exact RamareSaouter2003.prime_interval_nat_ladder_grp070 n (by omega) (by omega)
          · -- n <= 46148248066457
            exact RamareSaouter2003.prime_interval_nat_ladder_grp069 n (by omega) (by omega)
        · -- n <= 40783396349303
          rcases Nat.lt_or_ge 36042222348907 n with h10 | h10
          · -- n > 36042222348907
            exact RamareSaouter2003.prime_interval_nat_ladder_grp068 n (by omega) (by omega)
          · -- n <= 36042222348907
            exact RamareSaouter2003.prime_interval_nat_ladder_grp067 n (by omega) (by omega)
  · -- n <= 31852221937607
    rcases Nat.lt_or_ge 8179930630579 n with h4 | h4
    · -- n > 8179930630579
      rcases Nat.lt_or_ge 15174303375743 n with h6 | h6
      · -- n > 15174303375743
        rcases Nat.lt_or_ge 21984887510237 n with h8 | h8
        · -- n > 21984887510237
          rcases Nat.lt_or_ge 24876889450507 n with h10 | h10
          · -- n > 24876889450507
            rcases Nat.lt_or_ge 28149319776593 n with h12 | h12
            · -- n > 28149319776593
              exact RamareSaouter2003.prime_interval_nat_ladder_grp066 n (by omega) (by omega)
            · -- n <= 28149319776593
              exact RamareSaouter2003.prime_interval_nat_ladder_grp065 n (by omega) (by omega)
          · -- n <= 24876889450507
            exact RamareSaouter2003.prime_interval_nat_ladder_grp064 n (by omega) (by omega)
        · -- n <= 21984887510237
          rcases Nat.lt_or_ge 17170407053213 n with h10 | h10
          · -- n > 17170407053213
            rcases Nat.lt_or_ge 19429088181631 n with h12 | h12
            · -- n > 19429088181631
              exact RamareSaouter2003.prime_interval_nat_ladder_grp063 n (by omega) (by omega)
            · -- n <= 19429088181631
              exact RamareSaouter2003.prime_interval_nat_ladder_grp062 n (by omega) (by omega)
          · -- n <= 17170407053213
            exact RamareSaouter2003.prime_interval_nat_ladder_grp061 n (by omega) (by omega)
      · -- n <= 15174303375743
        rcases Nat.lt_or_ge 10473534734783 n with h8 | h8
        · -- n > 10473534734783
          rcases Nat.lt_or_ge 11851275819517 n with h10 | h10
          · -- n > 11851275819517
            rcases Nat.lt_or_ge 13410251849639 n with h12 | h12
            · -- n > 13410251849639
              exact RamareSaouter2003.prime_interval_nat_ladder_grp060 n (by omega) (by omega)
            · -- n <= 13410251849639
              exact RamareSaouter2003.prime_interval_nat_ladder_grp059 n (by omega) (by omega)
          · -- n <= 11851275819517
            exact RamareSaouter2003.prime_interval_nat_ladder_grp058 n (by omega) (by omega)
        · -- n <= 10473534734783
          rcases Nat.lt_or_ge 9255959571041 n with h10 | h10
          · -- n > 9255959571041
            exact RamareSaouter2003.prime_interval_nat_ladder_grp057 n (by omega) (by omega)
          · -- n <= 9255959571041
            exact RamareSaouter2003.prime_interval_nat_ladder_grp056 n (by omega) (by omega)
    · -- n <= 8179930630579
      rcases Nat.lt_or_ge 3896894525047 n with h6 | h6
      · -- n > 3896894525047
        rcases Nat.lt_or_ge 5645912403713 n with h8 | h8
        · -- n > 5645912403713
          rcases Nat.lt_or_ge 6388603926769 n with h10 | h10
          · -- n > 6388603926769
            rcases Nat.lt_or_ge 7228992803521 n with h12 | h12
            · -- n > 7228992803521
              exact RamareSaouter2003.prime_interval_nat_ladder_grp055 n (by omega) (by omega)
            · -- n <= 7228992803521
              exact RamareSaouter2003.prime_interval_nat_ladder_grp054 n (by omega) (by omega)
          · -- n <= 6388603926769
            exact RamareSaouter2003.prime_interval_nat_ladder_grp053 n (by omega) (by omega)
        · -- n <= 5645912403713
          rcases Nat.lt_or_ge 4409511496801 n with h10 | h10
          · -- n > 4409511496801
            rcases Nat.lt_or_ge 4989560667149 n with h12 | h12
            · -- n > 4989560667149
              exact RamareSaouter2003.prime_interval_nat_ladder_grp052 n (by omega) (by omega)
            · -- n <= 4989560667149
              exact RamareSaouter2003.prime_interval_nat_ladder_grp051 n (by omega) (by omega)
          · -- n <= 4409511496801
            exact RamareSaouter2003.prime_interval_nat_ladder_grp050 n (by omega) (by omega)
      · -- n <= 3896894525047
        rcases Nat.lt_or_ge 2681425988221 n with h8 | h8
        · -- n > 2681425988221
          rcases Nat.lt_or_ge 3042386133557 n with h10 | h10
          · -- n > 3042386133557
            rcases Nat.lt_or_ge 3443870585447 n with h12 | h12
            · -- n > 3443870585447
              exact RamareSaouter2003.prime_interval_nat_ladder_grp049 n (by omega) (by omega)
            · -- n <= 3443870585447
              exact RamareSaouter2003.prime_interval_nat_ladder_grp048 n (by omega) (by omega)
          · -- n <= 3042386133557
            exact RamareSaouter2003.prime_interval_nat_ladder_grp047 n (by omega) (by omega)
        · -- n <= 2681425988221
          rcases Nat.lt_or_ge 2363065123879 n with h10 | h10
          · -- n > 2363065123879
            exact RamareSaouter2003.prime_interval_nat_ladder_grp046 n (by omega) (by omega)
          · -- n <= 2363065123879
            exact RamareSaouter2003.prime_interval_nat_ladder_grp045 n (by omega) (by omega)
