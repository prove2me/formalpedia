-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_sgrp3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T00:13:01.615154+00:00
-- url     : https://prove2.me/submissions/dd7868c0-37f8-4378-992e-296b32ab120a

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp100
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp132

theorem solution (n : Nat)
    (hn : 570899461905341 < n) (hupper : n <= 286750217619026779) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 12791132576439523 n with h2 | h2
  · -- n > 12791132576439523
    rcases Nat.lt_or_ge 60561120261956563 n with h4 | h4
    · -- n > 60561120261956563
      rcases Nat.lt_or_ge 122786617740997081 n with h6 | h6
      · -- n > 122786617740997081
        rcases Nat.lt_or_ge 187640393798056393 n with h8 | h8
        · -- n > 187640393798056393
          rcases Nat.lt_or_ge 216131755642320989 n with h10 | h10
          · -- n > 216131755642320989
            rcases Nat.lt_or_ge 248949425222306737 n with h12 | h12
            · -- n > 248949425222306737
              exact RamareSaouter2003.prime_interval_nat_ladder_grp132 n (by omega) (by omega)
            · -- n <= 248949425222306737
              exact RamareSaouter2003.prime_interval_nat_ladder_grp131 n (by omega) (by omega)
          · -- n <= 216131755642320989
            exact RamareSaouter2003.prime_interval_nat_ladder_grp130 n (by omega) (by omega)
        · -- n <= 187640393798056393
          rcases Nat.lt_or_ge 141430315807842023 n with h10 | h10
          · -- n > 141430315807842023
            rcases Nat.lt_or_ge 162905024672217103 n with h12 | h12
            · -- n > 162905024672217103
              exact RamareSaouter2003.prime_interval_nat_ladder_grp129 n (by omega) (by omega)
            · -- n <= 162905024672217103
              exact RamareSaouter2003.prime_interval_nat_ladder_grp128 n (by omega) (by omega)
          · -- n <= 141430315807842023
            exact RamareSaouter2003.prime_interval_nat_ladder_grp127 n (by omega) (by omega)
      · -- n <= 122786617740997081
        rcases Nat.lt_or_ge 80348244495624299 n with h8 | h8
        · -- n > 80348244495624299
          rcases Nat.lt_or_ge 92548121498906519 n with h10 | h10
          · -- n > 92548121498906519
            rcases Nat.lt_or_ge 106600483443424039 n with h12 | h12
            · -- n > 106600483443424039
              exact RamareSaouter2003.prime_interval_nat_ladder_grp126 n (by omega) (by omega)
            · -- n <= 106600483443424039
              exact RamareSaouter2003.prime_interval_nat_ladder_grp125 n (by omega) (by omega)
          · -- n <= 92548121498906519
            exact RamareSaouter2003.prime_interval_nat_ladder_grp124 n (by omega) (by omega)
        · -- n <= 80348244495624299
          rcases Nat.lt_or_ge 69756529594900877 n with h10 | h10
          · -- n > 69756529594900877
            exact RamareSaouter2003.prime_interval_nat_ladder_grp123 n (by omega) (by omega)
          · -- n <= 69756529594900877
            exact RamareSaouter2003.prime_interval_nat_ladder_grp122 n (by omega) (by omega)
    · -- n <= 60561120261956563
      rcases Nat.lt_or_ge 25933117750214453 n with h6 | h6
      · -- n > 25933117750214453
        rcases Nat.lt_or_ge 39629926580993773 n with h8 | h8
        · -- n > 39629926580993773
          rcases Nat.lt_or_ge 45647159062049219 n with h10 | h10
          · -- n > 45647159062049219
            rcases Nat.lt_or_ge 52577951070072157 n with h12 | h12
            · -- n > 52577951070072157
              exact RamareSaouter2003.prime_interval_nat_ladder_grp121 n (by omega) (by omega)
            · -- n <= 52577951070072157
              exact RamareSaouter2003.prime_interval_nat_ladder_grp120 n (by omega) (by omega)
          · -- n <= 45647159062049219
            exact RamareSaouter2003.prime_interval_nat_ladder_grp119 n (by omega) (by omega)
        · -- n <= 39629926580993773
          rcases Nat.lt_or_ge 29870561433150253 n with h10 | h10
          · -- n > 29870561433150253
            rcases Nat.lt_or_ge 34405922531916673 n with h12 | h12
            · -- n > 34405922531916673
              exact RamareSaouter2003.prime_interval_nat_ladder_grp118 n (by omega) (by omega)
            · -- n <= 34405922531916673
              exact RamareSaouter2003.prime_interval_nat_ladder_grp117 n (by omega) (by omega)
          · -- n <= 29870561433150253
            exact RamareSaouter2003.prime_interval_nat_ladder_grp116 n (by omega) (by omega)
      · -- n <= 25933117750214453
        rcases Nat.lt_or_ge 16970173954204477 n with h8 | h8
        · -- n > 16970173954204477
          rcases Nat.lt_or_ge 19546801688263991 n with h10 | h10
          · -- n > 19546801688263991
            rcases Nat.lt_or_ge 22514638705499333 n with h12 | h12
            · -- n > 22514638705499333
              exact RamareSaouter2003.prime_interval_nat_ladder_grp115 n (by omega) (by omega)
            · -- n <= 22514638705499333
              exact RamareSaouter2003.prime_interval_nat_ladder_grp114 n (by omega) (by omega)
          · -- n <= 19546801688263991
            exact RamareSaouter2003.prime_interval_nat_ladder_grp113 n (by omega) (by omega)
        · -- n <= 16970173954204477
          rcases Nat.lt_or_ge 14733209110173557 n with h10 | h10
          · -- n > 14733209110173557
            exact RamareSaouter2003.prime_interval_nat_ladder_grp112 n (by omega) (by omega)
          · -- n <= 14733209110173557
            exact RamareSaouter2003.prime_interval_nat_ladder_grp111 n (by omega) (by omega)
  · -- n <= 12791132576439523
    rcases Nat.lt_or_ge 2701984647071959 n with h4 | h4
    · -- n > 2701984647071959
      rcases Nat.lt_or_ge 5477696691841147 n with h6 | h6
      · -- n > 5477696691841147
        rcases Nat.lt_or_ge 8370471890560501 n with h8 | h8
        · -- n > 8370471890560501
          rcases Nat.lt_or_ge 9641307945289051 n with h10 | h10
          · -- n > 9641307945289051
            rcases Nat.lt_or_ge 11105084835698311 n with h12 | h12
            · -- n > 11105084835698311
              exact RamareSaouter2003.prime_interval_nat_ladder_grp110 n (by omega) (by omega)
            · -- n <= 11105084835698311
              exact RamareSaouter2003.prime_interval_nat_ladder_grp109 n (by omega) (by omega)
          · -- n <= 9641307945289051
            exact RamareSaouter2003.prime_interval_nat_ladder_grp108 n (by omega) (by omega)
        · -- n <= 8370471890560501
          rcases Nat.lt_or_ge 6309300846480967 n with h10 | h10
          · -- n > 6309300846480967
            rcases Nat.lt_or_ge 7267171176941339 n with h12 | h12
            · -- n > 7267171176941339
              exact RamareSaouter2003.prime_interval_nat_ladder_grp107 n (by omega) (by omega)
            · -- n <= 7267171176941339
              exact RamareSaouter2003.prime_interval_nat_ladder_grp106 n (by omega) (by omega)
          · -- n <= 6309300846480967
            exact RamareSaouter2003.prime_interval_nat_ladder_grp105 n (by omega) (by omega)
      · -- n <= 5477696691841147
        rcases Nat.lt_or_ge 3584629562138893 n with h8 | h8
        · -- n > 3584629562138893
          rcases Nat.lt_or_ge 4128840276810539 n with h10 | h10
          · -- n > 4128840276810539
            rcases Nat.lt_or_ge 4755668462802073 n with h12 | h12
            · -- n > 4755668462802073
              exact RamareSaouter2003.prime_interval_nat_ladder_grp104 n (by omega) (by omega)
            · -- n <= 4755668462802073
              exact RamareSaouter2003.prime_interval_nat_ladder_grp103 n (by omega) (by omega)
          · -- n <= 4128840276810539
            exact RamareSaouter2003.prime_interval_nat_ladder_grp102 n (by omega) (by omega)
        · -- n <= 3584629562138893
          rcases Nat.lt_or_ge 3112164993040603 n with h10 | h10
          · -- n > 3112164993040603
            exact RamareSaouter2003.prime_interval_nat_ladder_grp101 n (by omega) (by omega)
          · -- n <= 3112164993040603
            exact RamareSaouter2003.prime_interval_nat_ladder_grp100 n (by omega) (by omega)
    · -- n <= 2701984647071959
      rcases Nat.lt_or_ge 1157209303635617 n with h6 | h6
      · -- n > 1157209303635617
        rcases Nat.lt_or_ge 1768250287586501 n with h8 | h8
        · -- n > 1768250287586501
          rcases Nat.lt_or_ge 2036672748741173 n with h10 | h10
          · -- n > 2036672748741173
            rcases Nat.lt_or_ge 2345869641159829 n with h12 | h12
            · -- n > 2345869641159829
              exact RamareSaouter2003.prime_interval_nat_ladder_grp099 n (by omega) (by omega)
            · -- n <= 2345869641159829
              exact RamareSaouter2003.prime_interval_nat_ladder_grp098 n (by omega) (by omega)
          · -- n <= 2036672748741173
            exact RamareSaouter2003.prime_interval_nat_ladder_grp097 n (by omega) (by omega)
        · -- n <= 1768250287586501
          rcases Nat.lt_or_ge 1332869397939077 n with h10 | h10
          · -- n > 1332869397939077
            rcases Nat.lt_or_ge 1535198451695543 n with h12 | h12
            · -- n > 1535198451695543
              exact RamareSaouter2003.prime_interval_nat_ladder_grp096 n (by omega) (by omega)
            · -- n <= 1535198451695543
              exact RamareSaouter2003.prime_interval_nat_ladder_grp095 n (by omega) (by omega)
          · -- n <= 1332869397939077
            exact RamareSaouter2003.prime_interval_nat_ladder_grp094 n (by omega) (by omega)
      · -- n <= 1157209303635617
        rcases Nat.lt_or_ge 757347815694311 n with h8 | h8
        · -- n > 757347815694311
          rcases Nat.lt_or_ge 872308179808937 n with h10 | h10
          · -- n > 872308179808937
            rcases Nat.lt_or_ge 1004703773149963 n with h12 | h12
            · -- n > 1004703773149963
              exact RamareSaouter2003.prime_interval_nat_ladder_grp093 n (by omega) (by omega)
            · -- n <= 1004703773149963
              exact RamareSaouter2003.prime_interval_nat_ladder_grp092 n (by omega) (by omega)
          · -- n <= 872308179808937
            exact RamareSaouter2003.prime_interval_nat_ladder_grp091 n (by omega) (by omega)
        · -- n <= 757347815694311
          rcases Nat.lt_or_ge 657550128634237 n with h10 | h10
          · -- n > 657550128634237
            exact RamareSaouter2003.prime_interval_nat_ladder_grp090 n (by omega) (by omega)
          · -- n <= 657550128634237
            exact RamareSaouter2003.prime_interval_nat_ladder_grp089 n (by omega) (by omega)
