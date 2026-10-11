-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T04:23:02.592775+00:00
-- url     : https://prove2.me/submissions/63e23799-2d92-4ae8-bd40-83f230307486

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01200

theorem solution (n : Nat)
    (hn : 147252479863 < n) (hupper : n <= 166837303537) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 156736449797 n with h2 | h2
  · -- n > 156736449797
    rcases Nat.lt_or_ge 161505438673 n with h4 | h4
    · -- n > 161505438673
      rcases Nat.lt_or_ge 163944589183 n with h6 | h6
      · -- n > 163944589183
        rcases Nat.lt_or_ge 165178073603 n with h8 | h8
        · -- n > 165178073603
          rcases Nat.lt_or_ge 166005596287 n with h10 | h10
          · -- n > 166005596287
            rcases Nat.lt_or_ge 166420925521 n with h12 | h12
            · -- n > 166420925521
              exact RamareSaouter2003.prime_interval_nat_ladder_c01200 n (by omega) (by omega)
            · -- n <= 166420925521
              exact RamareSaouter2003.prime_interval_nat_ladder_c01199 n (by omega) (by omega)
          · -- n <= 166005596287
            rcases Nat.lt_or_ge 165591313213 n with h12 | h12
            · -- n > 165591313213
              exact RamareSaouter2003.prime_interval_nat_ladder_c01198 n (by omega) (by omega)
            · -- n <= 165591313213
              exact RamareSaouter2003.prime_interval_nat_ladder_c01197 n (by omega) (by omega)
        · -- n <= 165178073603
          rcases Nat.lt_or_ge 164354714233 n with h10 | h10
          · -- n > 164354714233
            rcases Nat.lt_or_ge 164765874829 n with h12 | h12
            · -- n > 164765874829
              exact RamareSaouter2003.prime_interval_nat_ladder_c01196 n (by omega) (by omega)
            · -- n <= 164765874829
              exact RamareSaouter2003.prime_interval_nat_ladder_c01195 n (by omega) (by omega)
          · -- n <= 164354714233
            exact RamareSaouter2003.prime_interval_nat_ladder_c01194 n (by omega) (by omega)
      · -- n <= 163944589183
        rcases Nat.lt_or_ge 162720401149 n with h8 | h8
        · -- n > 162720401149
          rcases Nat.lt_or_ge 163127435299 n with h10 | h10
          · -- n > 163127435299
            rcases Nat.lt_or_ge 163535497043 n with h12 | h12
            · -- n > 163535497043
              exact RamareSaouter2003.prime_interval_nat_ladder_c01193 n (by omega) (by omega)
            · -- n <= 163535497043
              exact RamareSaouter2003.prime_interval_nat_ladder_c01192 n (by omega) (by omega)
          · -- n <= 163127435299
            exact RamareSaouter2003.prime_interval_nat_ladder_c01191 n (by omega) (by omega)
        · -- n <= 162720401149
          rcases Nat.lt_or_ge 161909405459 n with h10 | h10
          · -- n > 161909405459
            rcases Nat.lt_or_ge 162314392111 n with h12 | h12
            · -- n > 162314392111
              exact RamareSaouter2003.prime_interval_nat_ladder_c01190 n (by omega) (by omega)
            · -- n <= 162314392111
              exact RamareSaouter2003.prime_interval_nat_ladder_c01189 n (by omega) (by omega)
          · -- n <= 161909405459
            exact RamareSaouter2003.prime_interval_nat_ladder_c01188 n (by omega) (by omega)
    · -- n <= 161505438673
      rcases Nat.lt_or_ge 159102910493 n with h6 | h6
      · -- n > 159102910493
        rcases Nat.lt_or_ge 160299631637 n with h8 | h8
        · -- n > 160299631637
          rcases Nat.lt_or_ge 160700554367 n with h10 | h10
          · -- n > 160700554367
            rcases Nat.lt_or_ge 161102489167 n with h12 | h12
            · -- n > 161102489167
              exact RamareSaouter2003.prime_interval_nat_ladder_c01187 n (by omega) (by omega)
            · -- n <= 161102489167
              exact RamareSaouter2003.prime_interval_nat_ladder_c01186 n (by omega) (by omega)
          · -- n <= 160700554367
            exact RamareSaouter2003.prime_interval_nat_ladder_c01185 n (by omega) (by omega)
        · -- n <= 160299631637
          rcases Nat.lt_or_ge 159500812259 n with h10 | h10
          · -- n > 159500812259
            rcases Nat.lt_or_ge 159899718467 n with h12 | h12
            · -- n > 159899718467
              exact RamareSaouter2003.prime_interval_nat_ladder_c01184 n (by omega) (by omega)
            · -- n <= 159899718467
              exact RamareSaouter2003.prime_interval_nat_ladder_c01183 n (by omega) (by omega)
          · -- n <= 159500812259
            exact RamareSaouter2003.prime_interval_nat_ladder_c01182 n (by omega) (by omega)
      · -- n <= 159102910493
        rcases Nat.lt_or_ge 157915205957 n with h8 | h8
        · -- n > 157915205957
          rcases Nat.lt_or_ge 158310109849 n with h10 | h10
          · -- n > 158310109849
            rcases Nat.lt_or_ge 158706010517 n with h12 | h12
            · -- n > 158706010517
              exact RamareSaouter2003.prime_interval_nat_ladder_c01181 n (by omega) (by omega)
            · -- n <= 158706010517
              exact RamareSaouter2003.prime_interval_nat_ladder_c01180 n (by omega) (by omega)
          · -- n <= 158310109849
            exact RamareSaouter2003.prime_interval_nat_ladder_c01179 n (by omega) (by omega)
        · -- n <= 157915205957
          rcases Nat.lt_or_ge 157128378497 n with h10 | h10
          · -- n > 157128378497
            rcases Nat.lt_or_ge 157521296453 n with h12 | h12
            · -- n > 157521296453
              exact RamareSaouter2003.prime_interval_nat_ladder_c01178 n (by omega) (by omega)
            · -- n <= 157521296453
              exact RamareSaouter2003.prime_interval_nat_ladder_c01177 n (by omega) (by omega)
          · -- n <= 157128378497
            exact RamareSaouter2003.prime_interval_nat_ladder_c01176 n (by omega) (by omega)
  · -- n <= 156736449797
    rcases Nat.lt_or_ge 151730258081 n with h4 | h4
    · -- n > 151730258081
      rcases Nat.lt_or_ge 154020435683 n with h6 | h6
      · -- n > 154020435683
        rcases Nat.lt_or_ge 155178576569 n with h8 | h8
        · -- n > 155178576569
          rcases Nat.lt_or_ge 155955549829 n with h10 | h10
          · -- n > 155955549829
            rcases Nat.lt_or_ge 156345507709 n with h12 | h12
            · -- n > 156345507709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01175 n (by omega) (by omega)
            · -- n <= 156345507709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01174 n (by omega) (by omega)
          · -- n <= 155955549829
            rcases Nat.lt_or_ge 155566573621 n with h12 | h12
            · -- n > 155566573621
              exact RamareSaouter2003.prime_interval_nat_ladder_c01173 n (by omega) (by omega)
            · -- n <= 155566573621
              exact RamareSaouter2003.prime_interval_nat_ladder_c01172 n (by omega) (by omega)
        · -- n <= 155178576569
          rcases Nat.lt_or_ge 154405510099 n with h10 | h10
          · -- n > 154405510099
            rcases Nat.lt_or_ge 154791556261 n with h12 | h12
            · -- n > 154791556261
              exact RamareSaouter2003.prime_interval_nat_ladder_c01171 n (by omega) (by omega)
            · -- n <= 154791556261
              exact RamareSaouter2003.prime_interval_nat_ladder_c01170 n (by omega) (by omega)
          · -- n <= 154405510099
            exact RamareSaouter2003.prime_interval_nat_ladder_c01169 n (by omega) (by omega)
      · -- n <= 154020435683
        rcases Nat.lt_or_ge 152871018367 n with h8 | h8
        · -- n > 152871018367
          rcases Nat.lt_or_ge 153253192361 n with h10 | h10
          · -- n > 153253192361
            rcases Nat.lt_or_ge 153636330539 n with h12 | h12
            · -- n > 153636330539
              exact RamareSaouter2003.prime_interval_nat_ladder_c01168 n (by omega) (by omega)
            · -- n <= 153636330539
              exact RamareSaouter2003.prime_interval_nat_ladder_c01167 n (by omega) (by omega)
          · -- n <= 153253192361
            exact RamareSaouter2003.prime_interval_nat_ladder_c01166 n (by omega) (by omega)
        · -- n <= 152871018367
          rcases Nat.lt_or_ge 152109553699 n with h10 | h10
          · -- n > 152109553699
            rcases Nat.lt_or_ge 152489806289 n with h12 | h12
            · -- n > 152489806289
              exact RamareSaouter2003.prime_interval_nat_ladder_c01165 n (by omega) (by omega)
            · -- n <= 152489806289
              exact RamareSaouter2003.prime_interval_nat_ladder_c01164 n (by omega) (by omega)
          · -- n <= 152109553699
            exact RamareSaouter2003.prime_interval_nat_ladder_c01163 n (by omega) (by omega)
    · -- n <= 151730258081
      rcases Nat.lt_or_ge 149474446207 n with h6 | h6
      · -- n > 149474446207
        rcases Nat.lt_or_ge 150598089107 n with h8 | h8
        · -- n > 150598089107
          rcases Nat.lt_or_ge 150974528213 n with h10 | h10
          · -- n > 150974528213
            rcases Nat.lt_or_ge 151351917053 n with h12 | h12
            · -- n > 151351917053
              exact RamareSaouter2003.prime_interval_nat_ladder_c01162 n (by omega) (by omega)
            · -- n <= 151351917053
              exact RamareSaouter2003.prime_interval_nat_ladder_c01161 n (by omega) (by omega)
          · -- n <= 150974528213
            exact RamareSaouter2003.prime_interval_nat_ladder_c01160 n (by omega) (by omega)
        · -- n <= 150598089107
          rcases Nat.lt_or_ge 149848050491 n with h10 | h10
          · -- n > 149848050491
            rcases Nat.lt_or_ge 150222597331 n with h12 | h12
            · -- n > 150222597331
              exact RamareSaouter2003.prime_interval_nat_ladder_c01159 n (by omega) (by omega)
            · -- n <= 150222597331
              exact RamareSaouter2003.prime_interval_nat_ladder_c01158 n (by omega) (by omega)
          · -- n <= 149848050491
            exact RamareSaouter2003.prime_interval_nat_ladder_c01157 n (by omega) (by omega)
      · -- n <= 149474446207
        rcases Nat.lt_or_ge 148359264541 n with h8 | h8
        · -- n > 148359264541
          rcases Nat.lt_or_ge 148730055581 n with h10 | h10
          · -- n > 148730055581
            rcases Nat.lt_or_ge 149101782019 n with h12 | h12
            · -- n > 149101782019
              exact RamareSaouter2003.prime_interval_nat_ladder_c01156 n (by omega) (by omega)
            · -- n <= 149101782019
              exact RamareSaouter2003.prime_interval_nat_ladder_c01155 n (by omega) (by omega)
          · -- n <= 148730055581
            exact RamareSaouter2003.prime_interval_nat_ladder_c01154 n (by omega) (by omega)
        · -- n <= 148359264541
          rcases Nat.lt_or_ge 147620479051 n with h10 | h10
          · -- n > 147620479051
            rcases Nat.lt_or_ge 147989406491 n with h12 | h12
            · -- n > 147989406491
              exact RamareSaouter2003.prime_interval_nat_ladder_c01153 n (by omega) (by omega)
            · -- n <= 147989406491
              exact RamareSaouter2003.prime_interval_nat_ladder_c01152 n (by omega) (by omega)
          · -- n <= 147620479051
            exact RamareSaouter2003.prime_interval_nat_ladder_c01151 n (by omega) (by omega)
