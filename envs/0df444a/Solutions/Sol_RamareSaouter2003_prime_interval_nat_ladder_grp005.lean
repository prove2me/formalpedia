-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T16:16:02.421041+00:00
-- url     : https://prove2.me/submissions/426d2787-adbe-49c7-9163-972c70333574

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00250

theorem solution (n : Nat)
    (hn : 16558044781 < n) (hupper : n <= 18481081387) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 17491971733 n with h2 | h2
  · -- n > 17491971733
    rcases Nat.lt_or_ge 17959652959 n with h4 | h4
    · -- n > 17959652959
      rcases Nat.lt_or_ge 18198375527 n with h6 | h6
      · -- n > 18198375527
        rcases Nat.lt_or_ge 18318977867 n with h8 | h8
        · -- n > 18318977867
          rcases Nat.lt_or_ge 18399843107 n with h10 | h10
          · -- n > 18399843107
            rcases Nat.lt_or_ge 18440415529 n with h12 | h12
            · -- n > 18440415529
              exact RamareSaouter2003.prime_interval_nat_ladder_c00250 n (by omega) (by omega)
            · -- n <= 18440415529
              exact RamareSaouter2003.prime_interval_nat_ladder_c00249 n (by omega) (by omega)
          · -- n <= 18399843107
            rcases Nat.lt_or_ge 18359363959 n with h12 | h12
            · -- n > 18359363959
              exact RamareSaouter2003.prime_interval_nat_ladder_c00248 n (by omega) (by omega)
            · -- n <= 18359363959
              exact RamareSaouter2003.prime_interval_nat_ladder_c00247 n (by omega) (by omega)
        · -- n <= 18318977867
          rcases Nat.lt_or_ge 18238483871 n with h10 | h10
          · -- n > 18238483871
            rcases Nat.lt_or_ge 18278684569 n with h12 | h12
            · -- n > 18278684569
              exact RamareSaouter2003.prime_interval_nat_ladder_c00246 n (by omega) (by omega)
            · -- n <= 18278684569
              exact RamareSaouter2003.prime_interval_nat_ladder_c00245 n (by omega) (by omega)
          · -- n <= 18238483871
            exact RamareSaouter2003.prime_interval_nat_ladder_c00244 n (by omega) (by omega)
      · -- n <= 18198375527
        rcases Nat.lt_or_ge 18078602483 n with h8 | h8
        · -- n > 18078602483
          rcases Nat.lt_or_ge 18118435051 n with h10 | h10
          · -- n > 18118435051
            rcases Nat.lt_or_ge 18158359321 n with h12 | h12
            · -- n > 18158359321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00243 n (by omega) (by omega)
            · -- n <= 18158359321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00242 n (by omega) (by omega)
          · -- n <= 18118435051
            exact RamareSaouter2003.prime_interval_nat_ladder_c00241 n (by omega) (by omega)
        · -- n <= 18078602483
          rcases Nat.lt_or_ge 17999211701 n with h10 | h10
          · -- n > 17999211701
            rcases Nat.lt_or_ge 18038861447 n with h12 | h12
            · -- n > 18038861447
              exact RamareSaouter2003.prime_interval_nat_ladder_c00240 n (by omega) (by omega)
            · -- n <= 18038861447
              exact RamareSaouter2003.prime_interval_nat_ladder_c00239 n (by omega) (by omega)
          · -- n <= 17999211701
            exact RamareSaouter2003.prime_interval_nat_ladder_c00238 n (by omega) (by omega)
    · -- n <= 17959652959
      rcases Nat.lt_or_ge 17724200609 n with h6 | h6
      · -- n > 17724200609
        rcases Nat.lt_or_ge 17841520909 n with h8 | h8
        · -- n > 17841520909
          rcases Nat.lt_or_ge 17880807761 n with h10 | h10
          · -- n > 17880807761
            rcases Nat.lt_or_ge 17920185053 n with h12 | h12
            · -- n > 17920185053
              exact RamareSaouter2003.prime_interval_nat_ladder_c00237 n (by omega) (by omega)
            · -- n <= 17920185053
              exact RamareSaouter2003.prime_interval_nat_ladder_c00236 n (by omega) (by omega)
          · -- n <= 17880807761
            exact RamareSaouter2003.prime_interval_nat_ladder_c00235 n (by omega) (by omega)
        · -- n <= 17841520909
          rcases Nat.lt_or_ge 17763217543 n with h10 | h10
          · -- n > 17763217543
            rcases Nat.lt_or_ge 17802324259 n with h12 | h12
            · -- n > 17802324259
              exact RamareSaouter2003.prime_interval_nat_ladder_c00234 n (by omega) (by omega)
            · -- n <= 17802324259
              exact RamareSaouter2003.prime_interval_nat_ladder_c00233 n (by omega) (by omega)
          · -- n <= 17763217543
            exact RamareSaouter2003.prime_interval_nat_ladder_c00232 n (by omega) (by omega)
      · -- n <= 17724200609
        rcases Nat.lt_or_ge 17607686171 n with h8 | h8
        · -- n > 17607686171
          rcases Nat.lt_or_ge 17646435091 n with h10 | h10
          · -- n > 17646435091
            rcases Nat.lt_or_ge 17685273181 n with h12 | h12
            · -- n > 17685273181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00231 n (by omega) (by omega)
            · -- n <= 17685273181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00230 n (by omega) (by omega)
          · -- n <= 17646435091
            exact RamareSaouter2003.prime_interval_nat_ladder_c00229 n (by omega) (by omega)
        · -- n <= 17607686171
          rcases Nat.lt_or_ge 17530454653 n with h10 | h10
          · -- n > 17530454653
            rcases Nat.lt_or_ge 17569026067 n with h12 | h12
            · -- n > 17569026067
              exact RamareSaouter2003.prime_interval_nat_ladder_c00228 n (by omega) (by omega)
            · -- n <= 17569026067
              exact RamareSaouter2003.prime_interval_nat_ladder_c00227 n (by omega) (by omega)
          · -- n <= 17530454653
            exact RamareSaouter2003.prime_interval_nat_ladder_c00226 n (by omega) (by omega)
  · -- n <= 17491971733
    rcases Nat.lt_or_ge 16999649767 n with h4 | h4
    · -- n > 16999649767
      rcases Nat.lt_or_ge 17225050937 n with h6 | h6
      · -- n > 17225050937
        rcases Nat.lt_or_ge 17338920601 n with h8 | h8
        · -- n > 17338920601
          rcases Nat.lt_or_ge 17415270491 n with h10 | h10
          · -- n > 17415270491
            rcases Nat.lt_or_ge 17453577067 n with h12 | h12
            · -- n > 17453577067
              exact RamareSaouter2003.prime_interval_nat_ladder_c00225 n (by omega) (by omega)
            · -- n <= 17453577067
              exact RamareSaouter2003.prime_interval_nat_ladder_c00224 n (by omega) (by omega)
          · -- n <= 17415270491
            rcases Nat.lt_or_ge 17377051729 n with h12 | h12
            · -- n > 17377051729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00223 n (by omega) (by omega)
            · -- n <= 17377051729
              exact RamareSaouter2003.prime_interval_nat_ladder_c00222 n (by omega) (by omega)
        · -- n <= 17338920601
          rcases Nat.lt_or_ge 17262920417 n with h10 | h10
          · -- n > 17262920417
            rcases Nat.lt_or_ge 17300876899 n with h12 | h12
            · -- n > 17300876899
              exact RamareSaouter2003.prime_interval_nat_ladder_c00221 n (by omega) (by omega)
            · -- n <= 17300876899
              exact RamareSaouter2003.prime_interval_nat_ladder_c00220 n (by omega) (by omega)
          · -- n <= 17262920417
            exact RamareSaouter2003.prime_interval_nat_ladder_c00219 n (by omega) (by omega)
      · -- n <= 17225050937
        rcases Nat.lt_or_ge 17111962537 n with h8 | h8
        · -- n > 17111962537
          rcases Nat.lt_or_ge 17149572169 n with h10 | h10
          · -- n > 17149572169
            rcases Nat.lt_or_ge 17187268249 n with h12 | h12
            · -- n > 17187268249
              exact RamareSaouter2003.prime_interval_nat_ladder_c00218 n (by omega) (by omega)
            · -- n <= 17187268249
              exact RamareSaouter2003.prime_interval_nat_ladder_c00217 n (by omega) (by omega)
          · -- n <= 17149572169
            exact RamareSaouter2003.prime_interval_nat_ladder_c00216 n (by omega) (by omega)
        · -- n <= 17111962537
          rcases Nat.lt_or_ge 17037001511 n with h10 | h10
          · -- n > 17037001511
            rcases Nat.lt_or_ge 17074439051 n with h12 | h12
            · -- n > 17074439051
              exact RamareSaouter2003.prime_interval_nat_ladder_c00215 n (by omega) (by omega)
            · -- n <= 17074439051
              exact RamareSaouter2003.prime_interval_nat_ladder_c00214 n (by omega) (by omega)
          · -- n <= 17037001511
            exact RamareSaouter2003.prime_interval_nat_ladder_c00213 n (by omega) (by omega)
    · -- n <= 16999649767
      rcases Nat.lt_or_ge 16777328921 n with h6 | h6
      · -- n > 16777328921
        rcases Nat.lt_or_ge 16888107043 n with h8 | h8
        · -- n > 16888107043
          rcases Nat.lt_or_ge 16925202719 n with h10 | h10
          · -- n > 16925202719
            rcases Nat.lt_or_ge 16962383567 n with h12 | h12
            · -- n > 16962383567
              exact RamareSaouter2003.prime_interval_nat_ladder_c00212 n (by omega) (by omega)
            · -- n <= 16962383567
              exact RamareSaouter2003.prime_interval_nat_ladder_c00211 n (by omega) (by omega)
          · -- n <= 16925202719
            exact RamareSaouter2003.prime_interval_nat_ladder_c00210 n (by omega) (by omega)
        · -- n <= 16888107043
          rcases Nat.lt_or_ge 16814170363 n with h10 | h10
          · -- n > 16814170363
            rcases Nat.lt_or_ge 16851096319 n with h12 | h12
            · -- n > 16851096319
              exact RamareSaouter2003.prime_interval_nat_ladder_c00209 n (by omega) (by omega)
            · -- n <= 16851096319
              exact RamareSaouter2003.prime_interval_nat_ladder_c00208 n (by omega) (by omega)
          · -- n <= 16814170363
            exact RamareSaouter2003.prime_interval_nat_ladder_c00207 n (by omega) (by omega)
      · -- n <= 16777328921
        rcases Nat.lt_or_ge 16667310059 n with h8 | h8
        · -- n > 16667310059
          rcases Nat.lt_or_ge 16703899021 n with h10 | h10
          · -- n > 16703899021
            rcases Nat.lt_or_ge 16740571849 n with h12 | h12
            · -- n > 16740571849
              exact RamareSaouter2003.prime_interval_nat_ladder_c00206 n (by omega) (by omega)
            · -- n <= 16740571849
              exact RamareSaouter2003.prime_interval_nat_ladder_c00205 n (by omega) (by omega)
          · -- n <= 16703899021
            exact RamareSaouter2003.prime_interval_nat_ladder_c00204 n (by omega) (by omega)
        · -- n <= 16667310059
          rcases Nat.lt_or_ge 16594383131 n with h10 | h10
          · -- n > 16594383131
            rcases Nat.lt_or_ge 16630804811 n with h12 | h12
            · -- n > 16630804811
              exact RamareSaouter2003.prime_interval_nat_ladder_c00203 n (by omega) (by omega)
            · -- n <= 16630804811
              exact RamareSaouter2003.prime_interval_nat_ladder_c00202 n (by omega) (by omega)
          · -- n <= 16594383131
            exact RamareSaouter2003.prime_interval_nat_ladder_c00201 n (by omega) (by omega)
