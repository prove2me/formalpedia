-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T03:45:05.536688+00:00
-- url     : https://prove2.me/submissions/a194e648-11bb-4283-b3ee-b3eef2f99a45

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01150

theorem solution (n : Nat)
    (hn : 129985561751 < n) (hupper : n <= 147252479863) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 138347396417 n with h2 | h2
  · -- n > 138347396417
    rcases Nat.lt_or_ge 142551898351 n with h4 | h4
    · -- n > 142551898351
      rcases Nat.lt_or_ge 144702279853 n with h6 | h6
      · -- n > 144702279853
        rcases Nat.lt_or_ge 145789718779 n with h8 | h8
        · -- n > 145789718779
          rcases Nat.lt_or_ge 146519256937 n with h10 | h10
          · -- n > 146519256937
            rcases Nat.lt_or_ge 146885406631 n with h12 | h12
            · -- n > 146885406631
              exact RamareSaouter2003.prime_interval_nat_ladder_c01150 n (by omega) (by omega)
            · -- n <= 146885406631
              exact RamareSaouter2003.prime_interval_nat_ladder_c01149 n (by omega) (by omega)
          · -- n <= 146519256937
            rcases Nat.lt_or_ge 146154028421 n with h12 | h12
            · -- n > 146154028421
              exact RamareSaouter2003.prime_interval_nat_ladder_c01148 n (by omega) (by omega)
            · -- n <= 146154028421
              exact RamareSaouter2003.prime_interval_nat_ladder_c01147 n (by omega) (by omega)
        · -- n <= 145789718779
          rcases Nat.lt_or_ge 145063846847 n with h10 | h10
          · -- n > 145063846847
            rcases Nat.lt_or_ge 145426325669 n with h12 | h12
            · -- n > 145426325669
              exact RamareSaouter2003.prime_interval_nat_ladder_c01146 n (by omega) (by omega)
            · -- n <= 145426325669
              exact RamareSaouter2003.prime_interval_nat_ladder_c01145 n (by omega) (by omega)
          · -- n <= 145063846847
            exact RamareSaouter2003.prime_interval_nat_ladder_c01144 n (by omega) (by omega)
      · -- n <= 144702279853
        rcases Nat.lt_or_ge 143623027049 n with h8 | h8
        · -- n > 143623027049
          rcases Nat.lt_or_ge 143981872241 n with h10 | h10
          · -- n > 143981872241
            rcases Nat.lt_or_ge 144341622419 n with h12 | h12
            · -- n > 144341622419
              exact RamareSaouter2003.prime_interval_nat_ladder_c01143 n (by omega) (by omega)
            · -- n <= 144341622419
              exact RamareSaouter2003.prime_interval_nat_ladder_c01142 n (by omega) (by omega)
          · -- n <= 143981872241
            exact RamareSaouter2003.prime_interval_nat_ladder_c01141 n (by omega) (by omega)
        · -- n <= 143623027049
          rcases Nat.lt_or_ge 142908042337 n with h10 | h10
          · -- n > 142908042337
            rcases Nat.lt_or_ge 143265084511 n with h12 | h12
            · -- n > 143265084511
              exact RamareSaouter2003.prime_interval_nat_ladder_c01140 n (by omega) (by omega)
            · -- n <= 143265084511
              exact RamareSaouter2003.prime_interval_nat_ladder_c01139 n (by omega) (by omega)
          · -- n <= 142908042337
            exact RamareSaouter2003.prime_interval_nat_ladder_c01138 n (by omega) (by omega)
    · -- n <= 142551898351
      rcases Nat.lt_or_ge 140433766591 n with h6 | h6
      · -- n > 140433766591
        rcases Nat.lt_or_ge 141488831903 n with h8 | h8
        · -- n > 141488831903
          rcases Nat.lt_or_ge 141842295379 n with h10 | h10
          · -- n > 141842295379
            rcases Nat.lt_or_ge 142196650117 n with h12 | h12
            · -- n > 142196650117
              exact RamareSaouter2003.prime_interval_nat_ladder_c01137 n (by omega) (by omega)
            · -- n <= 142196650117
              exact RamareSaouter2003.prime_interval_nat_ladder_c01136 n (by omega) (by omega)
          · -- n <= 141842295379
            exact RamareSaouter2003.prime_interval_nat_ladder_c01135 n (by omega) (by omega)
        · -- n <= 141488831903
          rcases Nat.lt_or_ge 140784569767 n with h10 | h10
          · -- n > 140784569767
            rcases Nat.lt_or_ge 141136257421 n with h12 | h12
            · -- n > 141136257421
              exact RamareSaouter2003.prime_interval_nat_ladder_c01134 n (by omega) (by omega)
            · -- n <= 141136257421
              exact RamareSaouter2003.prime_interval_nat_ladder_c01133 n (by omega) (by omega)
          · -- n <= 140784569767
            exact RamareSaouter2003.prime_interval_nat_ladder_c01132 n (by omega) (by omega)
      · -- n <= 140433766591
        rcases Nat.lt_or_ge 139386641521 n with h8 | h8
        · -- n > 139386641521
          rcases Nat.lt_or_ge 139734804707 n with h10 | h10
          · -- n > 139734804707
            rcases Nat.lt_or_ge 140083845647 n with h12 | h12
            · -- n > 140083845647
              exact RamareSaouter2003.prime_interval_nat_ladder_c01131 n (by omega) (by omega)
            · -- n <= 140083845647
              exact RamareSaouter2003.prime_interval_nat_ladder_c01130 n (by omega) (by omega)
          · -- n <= 139734804707
            exact RamareSaouter2003.prime_interval_nat_ladder_c01129 n (by omega) (by omega)
        · -- n <= 139386641521
          rcases Nat.lt_or_ge 138692939597 n with h10 | h10
          · -- n > 138692939597
            rcases Nat.lt_or_ge 139039353907 n with h12 | h12
            · -- n > 139039353907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01128 n (by omega) (by omega)
            · -- n <= 139039353907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01127 n (by omega) (by omega)
          · -- n <= 138692939597
            exact RamareSaouter2003.prime_interval_nat_ladder_c01126 n (by omega) (by omega)
  · -- n <= 138347396417
    rcases Nat.lt_or_ge 133933608521 n with h4 | h4
    · -- n > 133933608521
      rcases Nat.lt_or_ge 135952800553 n with h6 | h6
      · -- n > 135952800553
        rcases Nat.lt_or_ge 136973890751 n with h8 | h8
        · -- n > 136973890751
          rcases Nat.lt_or_ge 137658914581 n with h10 | h10
          · -- n > 137658914581
            rcases Nat.lt_or_ge 138002722163 n with h12 | h12
            · -- n > 138002722163
              exact RamareSaouter2003.prime_interval_nat_ladder_c01125 n (by omega) (by omega)
            · -- n <= 138002722163
              exact RamareSaouter2003.prime_interval_nat_ladder_c01124 n (by omega) (by omega)
          · -- n <= 137658914581
            rcases Nat.lt_or_ge 137315971489 n with h12 | h12
            · -- n > 137315971489
              exact RamareSaouter2003.prime_interval_nat_ladder_c01123 n (by omega) (by omega)
            · -- n <= 137315971489
              exact RamareSaouter2003.prime_interval_nat_ladder_c01122 n (by omega) (by omega)
        · -- n <= 136973890751
          rcases Nat.lt_or_ge 136292307509 n with h10 | h10
          · -- n > 136292307509
            rcases Nat.lt_or_ge 136632670241 n with h12 | h12
            · -- n > 136632670241
              exact RamareSaouter2003.prime_interval_nat_ladder_c01121 n (by omega) (by omega)
            · -- n <= 136632670241
              exact RamareSaouter2003.prime_interval_nat_ladder_c01120 n (by omega) (by omega)
          · -- n <= 136292307509
            exact RamareSaouter2003.prime_interval_nat_ladder_c01119 n (by omega) (by omega)
      · -- n <= 135952800553
        rcases Nat.lt_or_ge 134939392571 n with h8 | h8
        · -- n > 134939392571
          rcases Nat.lt_or_ge 135276345229 n with h10 | h10
          · -- n > 135276345229
            rcases Nat.lt_or_ge 135614147173 n with h12 | h12
            · -- n > 135614147173
              exact RamareSaouter2003.prime_interval_nat_ladder_c01118 n (by omega) (by omega)
            · -- n <= 135614147173
              exact RamareSaouter2003.prime_interval_nat_ladder_c01117 n (by omega) (by omega)
          · -- n <= 135276345229
            exact RamareSaouter2003.prime_interval_nat_ladder_c01116 n (by omega) (by omega)
        · -- n <= 134939392571
          rcases Nat.lt_or_ge 134268026341 n with h10 | h10
          · -- n > 134268026341
            rcases Nat.lt_or_ge 134603286971 n with h12 | h12
            · -- n > 134603286971
              exact RamareSaouter2003.prime_interval_nat_ladder_c01115 n (by omega) (by omega)
            · -- n <= 134603286971
              exact RamareSaouter2003.prime_interval_nat_ladder_c01114 n (by omega) (by omega)
          · -- n <= 134268026341
            exact RamareSaouter2003.prime_interval_nat_ladder_c01113 n (by omega) (by omega)
    · -- n <= 133933608521
      rcases Nat.lt_or_ge 131944681513 n with h6 | h6
      · -- n > 131944681513
        rcases Nat.lt_or_ge 132935390701 n with h8 | h8
        · -- n > 132935390701
          rcases Nat.lt_or_ge 133267292773 n with h10 | h10
          · -- n > 133267292773
            rcases Nat.lt_or_ge 133600031371 n with h12 | h12
            · -- n > 133600031371
              exact RamareSaouter2003.prime_interval_nat_ladder_c01112 n (by omega) (by omega)
            · -- n <= 133600031371
              exact RamareSaouter2003.prime_interval_nat_ladder_c01111 n (by omega) (by omega)
          · -- n <= 133267292773
            exact RamareSaouter2003.prime_interval_nat_ladder_c01110 n (by omega) (by omega)
        · -- n <= 132935390701
          rcases Nat.lt_or_ge 132274087087 n with h10 | h10
          · -- n > 132274087087
            rcases Nat.lt_or_ge 132604322803 n with h12 | h12
            · -- n > 132604322803
              exact RamareSaouter2003.prime_interval_nat_ladder_c01109 n (by omega) (by omega)
            · -- n <= 132604322803
              exact RamareSaouter2003.prime_interval_nat_ladder_c01108 n (by omega) (by omega)
          · -- n <= 132274087087
            exact RamareSaouter2003.prime_interval_nat_ladder_c01107 n (by omega) (by omega)
      · -- n <= 131944681513
        rcases Nat.lt_or_ge 130961424161 n with h8 | h8
        · -- n > 130961424161
          rcases Nat.lt_or_ge 131288352163 n with h10 | h10
          · -- n > 131288352163
            rcases Nat.lt_or_ge 131616103987 n with h12 | h12
            · -- n > 131616103987
              exact RamareSaouter2003.prime_interval_nat_ladder_c01106 n (by omega) (by omega)
            · -- n <= 131616103987
              exact RamareSaouter2003.prime_interval_nat_ladder_c01105 n (by omega) (by omega)
          · -- n <= 131288352163
            exact RamareSaouter2003.prime_interval_nat_ladder_c01104 n (by omega) (by omega)
        · -- n <= 130961424161
          rcases Nat.lt_or_ge 130310031013 n with h10 | h10
          · -- n > 130310031013
            rcases Nat.lt_or_ge 130635317789 n with h12 | h12
            · -- n > 130635317789
              exact RamareSaouter2003.prime_interval_nat_ladder_c01103 n (by omega) (by omega)
            · -- n <= 130635317789
              exact RamareSaouter2003.prime_interval_nat_ladder_c01102 n (by omega) (by omega)
          · -- n <= 130310031013
            exact RamareSaouter2003.prime_interval_nat_ladder_c01101 n (by omega) (by omega)
