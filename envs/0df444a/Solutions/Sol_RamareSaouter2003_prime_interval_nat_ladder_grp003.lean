-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T14:50:30.106051+00:00
-- url     : https://prove2.me/submissions/db58febb-0d05-4f55-a096-74ebca43934e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00150

theorem solution (n : Nat)
    (hn : 13313012261 < n) (hupper : n <= 14843139557) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 14056328347 n with h2 | h2
  · -- n > 14056328347
    rcases Nat.lt_or_ge 14428409717 n with h4 | h4
    · -- n > 14428409717
      rcases Nat.lt_or_ge 14618297543 n with h6 | h6
      · -- n > 14618297543
        rcases Nat.lt_or_ge 14714219309 n with h8 | h8
        · -- n > 14714219309
          rcases Nat.lt_or_ge 14778532507 n with h10 | h10
          · -- n > 14778532507
            rcases Nat.lt_or_ge 14810799247 n with h12 | h12
            · -- n > 14810799247
              exact RamareSaouter2003.prime_interval_nat_ladder_c00150 n (by omega) (by omega)
            · -- n <= 14810799247
              exact RamareSaouter2003.prime_interval_nat_ladder_c00149 n (by omega) (by omega)
          · -- n <= 14778532507
            rcases Nat.lt_or_ge 14746339271 n with h12 | h12
            · -- n > 14746339271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00148 n (by omega) (by omega)
            · -- n <= 14746339271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00147 n (by omega) (by omega)
        · -- n <= 14714219309
          rcases Nat.lt_or_ge 14650198649 n with h10 | h10
          · -- n > 14650198649
            rcases Nat.lt_or_ge 14682172471 n with h12 | h12
            · -- n > 14682172471
              exact RamareSaouter2003.prime_interval_nat_ladder_c00146 n (by omega) (by omega)
            · -- n <= 14682172471
              exact RamareSaouter2003.prime_interval_nat_ladder_c00145 n (by omega) (by omega)
          · -- n <= 14650198649
            exact RamareSaouter2003.prime_interval_nat_ladder_c00144 n (by omega) (by omega)
      · -- n <= 14618297543
        rcases Nat.lt_or_ge 14523029201 n with h8 | h8
        · -- n > 14523029201
          rcases Nat.lt_or_ge 14554712983 n with h10 | h10
          · -- n > 14554712983
            rcases Nat.lt_or_ge 14586469063 n with h12 | h12
            · -- n > 14586469063
              exact RamareSaouter2003.prime_interval_nat_ladder_c00143 n (by omega) (by omega)
            · -- n <= 14586469063
              exact RamareSaouter2003.prime_interval_nat_ladder_c00142 n (by omega) (by omega)
          · -- n <= 14554712983
            exact RamareSaouter2003.prime_interval_nat_ladder_c00141 n (by omega) (by omega)
        · -- n <= 14523029201
          rcases Nat.lt_or_ge 14459877701 n with h10 | h10
          · -- n > 14459877701
            rcases Nat.lt_or_ge 14491417469 n with h12 | h12
            · -- n > 14491417469
              exact RamareSaouter2003.prime_interval_nat_ladder_c00140 n (by omega) (by omega)
            · -- n <= 14491417469
              exact RamareSaouter2003.prime_interval_nat_ladder_c00139 n (by omega) (by omega)
          · -- n <= 14459877701
            exact RamareSaouter2003.prime_interval_nat_ladder_c00138 n (by omega) (by omega)
    · -- n <= 14428409717
      rcases Nat.lt_or_ge 14241098741 n with h6 | h6
      · -- n > 14241098741
        rcases Nat.lt_or_ge 14334434383 n with h8 | h8
        · -- n > 14334434383
          rcases Nat.lt_or_ge 14365688209 n with h10 | h10
          · -- n > 14365688209
            rcases Nat.lt_or_ge 14397013283 n with h12 | h12
            · -- n > 14397013283
              exact RamareSaouter2003.prime_interval_nat_ladder_c00137 n (by omega) (by omega)
            · -- n <= 14397013283
              exact RamareSaouter2003.prime_interval_nat_ladder_c00136 n (by omega) (by omega)
          · -- n <= 14365688209
            exact RamareSaouter2003.prime_interval_nat_ladder_c00135 n (by omega) (by omega)
        · -- n <= 14334434383
          rcases Nat.lt_or_ge 14272139851 n with h10 | h10
          · -- n > 14272139851
            rcases Nat.lt_or_ge 14303251681 n with h12 | h12
            · -- n > 14303251681
              exact RamareSaouter2003.prime_interval_nat_ladder_c00134 n (by omega) (by omega)
            · -- n <= 14303251681
              exact RamareSaouter2003.prime_interval_nat_ladder_c00133 n (by omega) (by omega)
          · -- n <= 14272139851
            exact RamareSaouter2003.prime_interval_nat_ladder_c00132 n (by omega) (by omega)
      · -- n <= 14241098741
        rcases Nat.lt_or_ge 14148398219 n with h8 | h8
        · -- n > 14148398219
          rcases Nat.lt_or_ge 14179228121 n with h10 | h10
          · -- n > 14179228121
            rcases Nat.lt_or_ge 14210128217 n with h12 | h12
            · -- n > 14210128217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00131 n (by omega) (by omega)
            · -- n <= 14210128217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00130 n (by omega) (by omega)
          · -- n <= 14179228121
            exact RamareSaouter2003.prime_interval_nat_ladder_c00129 n (by omega) (by omega)
        · -- n <= 14148398219
          rcases Nat.lt_or_ge 14086948537 n with h10 | h10
          · -- n > 14086948537
            rcases Nat.lt_or_ge 14117638387 n with h12 | h12
            · -- n > 14117638387
              exact RamareSaouter2003.prime_interval_nat_ladder_c00128 n (by omega) (by omega)
            · -- n <= 14117638387
              exact RamareSaouter2003.prime_interval_nat_ladder_c00127 n (by omega) (by omega)
          · -- n <= 14086948537
            exact RamareSaouter2003.prime_interval_nat_ladder_c00126 n (by omega) (by omega)
  · -- n <= 14056328347
    rcases Nat.lt_or_ge 13664537329 n with h4 | h4
    · -- n > 13664537329
      rcases Nat.lt_or_ge 13843925899 n with h6 | h6
      · -- n > 13843925899
        rcases Nat.lt_or_ge 13934541667 n with h8 | h8
        · -- n > 13934541667
          rcases Nat.lt_or_ge 13995296501 n with h10 | h10
          · -- n > 13995296501
            rcases Nat.lt_or_ge 14025777719 n with h12 | h12
            · -- n > 14025777719
              exact RamareSaouter2003.prime_interval_nat_ladder_c00125 n (by omega) (by omega)
            · -- n <= 14025777719
              exact RamareSaouter2003.prime_interval_nat_ladder_c00124 n (by omega) (by omega)
          · -- n <= 13995296501
            rcases Nat.lt_or_ge 13964884517 n with h12 | h12
            · -- n > 13964884517
              exact RamareSaouter2003.prime_interval_nat_ladder_c00123 n (by omega) (by omega)
            · -- n <= 13964884517
              exact RamareSaouter2003.prime_interval_nat_ladder_c00122 n (by omega) (by omega)
        · -- n <= 13934541667
          rcases Nat.lt_or_ge 13874062541 n with h10 | h10
          · -- n > 13874062541
            rcases Nat.lt_or_ge 13904267759 n with h12 | h12
            · -- n > 13904267759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00121 n (by omega) (by omega)
            · -- n <= 13904267759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00120 n (by omega) (by omega)
          · -- n <= 13874062541
            exact RamareSaouter2003.prime_interval_nat_ladder_c00119 n (by omega) (by omega)
      · -- n <= 13843925899
        rcases Nat.lt_or_ge 13753925869 n with h8 | h8
        · -- n > 13753925869
          rcases Nat.lt_or_ge 13783857727 n with h10 | h10
          · -- n > 13783857727
            rcases Nat.lt_or_ge 13813857697 n with h12 | h12
            · -- n > 13813857697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00118 n (by omega) (by omega)
            · -- n <= 13813857697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00117 n (by omega) (by omega)
          · -- n <= 13783857727
            exact RamareSaouter2003.prime_interval_nat_ladder_c00116 n (by omega) (by omega)
        · -- n <= 13753925869
          rcases Nat.lt_or_ge 13694265839 n with h10 | h10
          · -- n > 13694265839
            rcases Nat.lt_or_ge 13724061947 n with h12 | h12
            · -- n > 13724061947
              exact RamareSaouter2003.prime_interval_nat_ladder_c00115 n (by omega) (by omega)
            · -- n <= 13724061947
              exact RamareSaouter2003.prime_interval_nat_ladder_c00114 n (by omega) (by omega)
          · -- n <= 13694265839
            exact RamareSaouter2003.prime_interval_nat_ladder_c00113 n (by omega) (by omega)
    · -- n <= 13664537329
      rcases Nat.lt_or_ge 13487577473 n with h6 | h6
      · -- n > 13487577473
        rcases Nat.lt_or_ge 13575755989 n with h8 | h8
        · -- n > 13575755989
          rcases Nat.lt_or_ge 13605282577 n with h10 | h10
          · -- n > 13605282577
            rcases Nat.lt_or_ge 13634876293 n with h12 | h12
            · -- n > 13634876293
              exact RamareSaouter2003.prime_interval_nat_ladder_c00112 n (by omega) (by omega)
            · -- n <= 13634876293
              exact RamareSaouter2003.prime_interval_nat_ladder_c00111 n (by omega) (by omega)
          · -- n <= 13605282577
            exact RamareSaouter2003.prime_interval_nat_ladder_c00110 n (by omega) (by omega)
        · -- n <= 13575755989
          rcases Nat.lt_or_ge 13516903597 n with h10 | h10
          · -- n > 13516903597
            rcases Nat.lt_or_ge 13546296389 n with h12 | h12
            · -- n > 13546296389
              exact RamareSaouter2003.prime_interval_nat_ladder_c00109 n (by omega) (by omega)
            · -- n <= 13546296389
              exact RamareSaouter2003.prime_interval_nat_ladder_c00108 n (by omega) (by omega)
          · -- n <= 13516903597
            exact RamareSaouter2003.prime_interval_nat_ladder_c00107 n (by omega) (by omega)
      · -- n <= 13487577473
        rcases Nat.lt_or_ge 13399997753 n with h8 | h8
        · -- n > 13399997753
          rcases Nat.lt_or_ge 13429124693 n with h10 | h10
          · -- n > 13429124693
            rcases Nat.lt_or_ge 13458317879 n with h12 | h12
            · -- n > 13458317879
              exact RamareSaouter2003.prime_interval_nat_ladder_c00106 n (by omega) (by omega)
            · -- n <= 13458317879
              exact RamareSaouter2003.prime_interval_nat_ladder_c00105 n (by omega) (by omega)
          · -- n <= 13429124693
            exact RamareSaouter2003.prime_interval_nat_ladder_c00104 n (by omega) (by omega)
        · -- n <= 13399997753
          rcases Nat.lt_or_ge 13341941609 n with h10 | h10
          · -- n > 13341941609
            rcases Nat.lt_or_ge 13370936737 n with h12 | h12
            · -- n > 13370936737
              exact RamareSaouter2003.prime_interval_nat_ladder_c00103 n (by omega) (by omega)
            · -- n <= 13370936737
              exact RamareSaouter2003.prime_interval_nat_ladder_c00102 n (by omega) (by omega)
          · -- n <= 13341941609
            exact RamareSaouter2003.prime_interval_nat_ladder_c00101 n (by omega) (by omega)
