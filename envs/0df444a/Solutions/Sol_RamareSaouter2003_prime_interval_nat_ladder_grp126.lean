-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T22:22:05.102976+00:00
-- url     : https://prove2.me/submissions/614c4770-f4a7-448d-9194-2b10997cc18a

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06300

theorem solution (n : Nat)
    (hn : 106600483443424039 < n) (hupper : n <= 122786617740997081) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 114407647347655577 n with h2 | h2
  · -- n > 114407647347655577
    rcases Nat.lt_or_ge 118355679338672641 n with h4 | h4
    · -- n > 118355679338672641
      rcases Nat.lt_or_ge 120380515172761223 n with h6 | h6
      · -- n > 120380515172761223
        rcases Nat.lt_or_ge 121405902510004141 n with h8 | h8
        · -- n > 121405902510004141
          rcases Nat.lt_or_ge 122094318125156627 n with h10 | h10
          · -- n > 122094318125156627
            rcases Nat.lt_or_ge 122440003202026733 n with h12 | h12
            · -- n > 122440003202026733
              exact RamareSaouter2003.prime_interval_nat_ladder_c06300 n (by omega) (by omega)
            · -- n <= 122440003202026733
              exact RamareSaouter2003.prime_interval_nat_ladder_c06299 n (by omega) (by omega)
          · -- n <= 122094318125156627
            rcases Nat.lt_or_ge 121749622770292619 n with h12 | h12
            · -- n > 121749622770292619
              exact RamareSaouter2003.prime_interval_nat_ladder_c06298 n (by omega) (by omega)
            · -- n <= 121749622770292619
              exact RamareSaouter2003.prime_interval_nat_ladder_c06297 n (by omega) (by omega)
        · -- n <= 121405902510004141
          rcases Nat.lt_or_ge 120721339948680379 n with h10 | h10
          · -- n > 120721339948680379
            rcases Nat.lt_or_ge 121063137830700271 n with h12 | h12
            · -- n > 121063137830700271
              exact RamareSaouter2003.prime_interval_nat_ladder_c06296 n (by omega) (by omega)
            · -- n <= 121063137830700271
              exact RamareSaouter2003.prime_interval_nat_ladder_c06295 n (by omega) (by omega)
          · -- n <= 120721339948680379
            exact RamareSaouter2003.prime_interval_nat_ladder_c06294 n (by omega) (by omega)
      · -- n <= 120380515172761223
        rcases Nat.lt_or_ge 119363811589688051 n with h8 | h8
        · -- n > 119363811589688051
          rcases Nat.lt_or_ge 119701745408197361 n with h10 | h10
          · -- n > 119701745408197361
            rcases Nat.lt_or_ge 120040657244675471 n with h12 | h12
            · -- n > 120040657244675471
              exact RamareSaouter2003.prime_interval_nat_ladder_c06293 n (by omega) (by omega)
            · -- n <= 120040657244675471
              exact RamareSaouter2003.prime_interval_nat_ladder_c06292 n (by omega) (by omega)
          · -- n <= 119701745408197361
            exact RamareSaouter2003.prime_interval_nat_ladder_c06291 n (by omega) (by omega)
        · -- n <= 119363811589688051
          rcases Nat.lt_or_ge 118690779840681359 n with h10 | h10
          · -- n > 118690779840681359
            rcases Nat.lt_or_ge 119026812869483219 n with h12 | h12
            · -- n > 119026812869483219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06290 n (by omega) (by omega)
            · -- n <= 119026812869483219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06289 n (by omega) (by omega)
          · -- n <= 118690779840681359
            exact RamareSaouter2003.prime_interval_nat_ladder_c06288 n (by omega) (by omega)
    · -- n <= 118355679338672641
      rcases Nat.lt_or_ge 116364914023190941 n with h6 | h6
      · -- n > 116364914023190941
        rcases Nat.lt_or_ge 117356082677450921 n with h8 | h8
        · -- n > 117356082677450921
          rcases Nat.lt_or_ge 117688351323514513 n with h10 | h10
          · -- n > 117688351323514513
            rcases Nat.lt_or_ge 118021558269765713 n with h12 | h12
            · -- n > 118021558269765713
              exact RamareSaouter2003.prime_interval_nat_ladder_c06287 n (by omega) (by omega)
            · -- n <= 118021558269765713
              exact RamareSaouter2003.prime_interval_nat_ladder_c06286 n (by omega) (by omega)
          · -- n <= 117688351323514513
            exact RamareSaouter2003.prime_interval_nat_ladder_c06285 n (by omega) (by omega)
        · -- n <= 117356082677450921
          rcases Nat.lt_or_ge 116694372163098047 n with h10 | h10
          · -- n > 116694372163098047
            rcases Nat.lt_or_ge 117024755130583151 n with h12 | h12
            · -- n > 117024755130583151
              exact RamareSaouter2003.prime_interval_nat_ladder_c06284 n (by omega) (by omega)
            · -- n <= 117024755130583151
              exact RamareSaouter2003.prime_interval_nat_ladder_c06283 n (by omega) (by omega)
          · -- n <= 116694372163098047
            exact RamareSaouter2003.prime_interval_nat_ladder_c06282 n (by omega) (by omega)
      · -- n <= 116364914023190941
        rcases Nat.lt_or_ge 115382109778946809 n with h8 | h8
        · -- n > 115382109778946809
          rcases Nat.lt_or_ge 115708783406383901 n with h10 | h10
          · -- n > 115708783406383901
            rcases Nat.lt_or_ge 116036380081537403 n with h12 | h12
            · -- n > 116036380081537403
              exact RamareSaouter2003.prime_interval_nat_ladder_c06281 n (by omega) (by omega)
            · -- n <= 116036380081537403
              exact RamareSaouter2003.prime_interval_nat_ladder_c06280 n (by omega) (by omega)
          · -- n <= 115708783406383901
            exact RamareSaouter2003.prime_interval_nat_ladder_c06279 n (by omega) (by omega)
        · -- n <= 115382109778946809
          rcases Nat.lt_or_ge 114731529133929163 n with h10 | h10
          · -- n > 114731529133929163
            rcases Nat.lt_or_ge 115056363274498049 n with h12 | h12
            · -- n > 115056363274498049
              exact RamareSaouter2003.prime_interval_nat_ladder_c06278 n (by omega) (by omega)
            · -- n <= 115056363274498049
              exact RamareSaouter2003.prime_interval_nat_ladder_c06277 n (by omega) (by omega)
          · -- n <= 114731529133929163
            exact RamareSaouter2003.prime_interval_nat_ladder_c06276 n (by omega) (by omega)
  · -- n <= 114407647347655577
    rcases Nat.lt_or_ge 110279076384119267 n with h4 | h4
    · -- n > 110279076384119267
      rcases Nat.lt_or_ge 112165717262920351 n with h6 | h6
      · -- n > 112165717262920351
        rcases Nat.lt_or_ge 113121108106723967 n with h8 | h8
        · -- n > 113121108106723967
          rcases Nat.lt_or_ge 113762567167662821 n with h10 | h10
          · -- n > 113762567167662821
            rcases Nat.lt_or_ge 114084659726767511 n with h12 | h12
            · -- n > 114084659726767511
              exact RamareSaouter2003.prime_interval_nat_ladder_c06275 n (by omega) (by omega)
            · -- n <= 114084659726767511
              exact RamareSaouter2003.prime_interval_nat_ladder_c06274 n (by omega) (by omega)
          · -- n <= 113762567167662821
            rcases Nat.lt_or_ge 113441385935546219 n with h12 | h12
            · -- n > 113441385935546219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06273 n (by omega) (by omega)
            · -- n <= 113441385935546219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06272 n (by omega) (by omega)
        · -- n <= 113121108106723967
          rcases Nat.lt_or_ge 112483289134879583 n with h10 | h10
          · -- n > 112483289134879583
            rcases Nat.lt_or_ge 112801749186413951 n with h12 | h12
            · -- n > 112801749186413951
              exact RamareSaouter2003.prime_interval_nat_ladder_c06271 n (by omega) (by omega)
            · -- n <= 112801749186413951
              exact RamareSaouter2003.prime_interval_nat_ladder_c06270 n (by omega) (by omega)
          · -- n <= 112483289134879583
            exact RamareSaouter2003.prime_interval_nat_ladder_c06269 n (by omega) (by omega)
      · -- n <= 112165717262920351
        rcases Nat.lt_or_ge 111218377315004009 n with h8 | h8
        · -- n > 111218377315004009
          rcases Nat.lt_or_ge 111533265637107733 n with h10 | h10
          · -- n > 111533265637107733
            rcases Nat.lt_or_ge 111849045882146059 n with h12 | h12
            · -- n > 111849045882146059
              exact RamareSaouter2003.prime_interval_nat_ladder_c06268 n (by omega) (by omega)
            · -- n <= 111849045882146059
              exact RamareSaouter2003.prime_interval_nat_ladder_c06267 n (by omega) (by omega)
          · -- n <= 111533265637107733
            exact RamareSaouter2003.prime_interval_nat_ladder_c06266 n (by omega) (by omega)
        · -- n <= 111218377315004009
          rcases Nat.lt_or_ge 110591290241046059 n with h10 | h10
          · -- n > 110591290241046059
            rcases Nat.lt_or_ge 110904407719328141 n with h12 | h12
            · -- n > 110904407719328141
              exact RamareSaouter2003.prime_interval_nat_ladder_c06265 n (by omega) (by omega)
            · -- n <= 110904407719328141
              exact RamareSaouter2003.prime_interval_nat_ladder_c06264 n (by omega) (by omega)
          · -- n <= 110591290241046059
            exact RamareSaouter2003.prime_interval_nat_ladder_c06263 n (by omega) (by omega)
    · -- n <= 110279076384119267
      rcases Nat.lt_or_ge 108424167478593523 n with h6 | h6
      · -- n > 108424167478593523
        rcases Nat.lt_or_ge 109347685849068497 n with h8 | h8
        · -- n > 109347685849068497
          rcases Nat.lt_or_ge 109657264735810201 n with h10 | h10
          · -- n > 109657264735810201
            rcases Nat.lt_or_ge 109967736284317837 n with h12 | h12
            · -- n > 109967736284317837
              exact RamareSaouter2003.prime_interval_nat_ladder_c06262 n (by omega) (by omega)
            · -- n <= 109967736284317837
              exact RamareSaouter2003.prime_interval_nat_ladder_c06261 n (by omega) (by omega)
          · -- n <= 109657264735810201
            exact RamareSaouter2003.prime_interval_nat_ladder_c06260 n (by omega) (by omega)
        · -- n <= 109347685849068497
          rcases Nat.lt_or_ge 108731134091671409 n with h10 | h10
          · -- n > 108731134091671409
            rcases Nat.lt_or_ge 109038979759094299 n with h12 | h12
            · -- n > 109038979759094299
              exact RamareSaouter2003.prime_interval_nat_ladder_c06259 n (by omega) (by omega)
            · -- n <= 109038979759094299
              exact RamareSaouter2003.prime_interval_nat_ladder_c06258 n (by omega) (by omega)
          · -- n <= 108731134091671409
            exact RamareSaouter2003.prime_interval_nat_ladder_c06257 n (by omega) (by omega)
      · -- n <= 108424167478593523
        rcases Nat.lt_or_ge 107508432567857033 n with h8 | h8
        · -- n > 107508432567857033
          rcases Nat.lt_or_ge 107812811317426807 n with h10 | h10
          · -- n > 107812811317426807
            rcases Nat.lt_or_ge 108118055668323637 n with h12 | h12
            · -- n > 108118055668323637
              exact RamareSaouter2003.prime_interval_nat_ladder_c06256 n (by omega) (by omega)
            · -- n <= 108118055668323637
              exact RamareSaouter2003.prime_interval_nat_ladder_c06255 n (by omega) (by omega)
          · -- n <= 107812811317426807
            exact RamareSaouter2003.prime_interval_nat_ladder_c06254 n (by omega) (by omega)
        · -- n <= 107508432567857033
          rcases Nat.lt_or_ge 106902290121949957 n with h10 | h10
          · -- n > 106902290121949957
            rcases Nat.lt_or_ge 107204941204112207 n with h12 | h12
            · -- n > 107204941204112207
              exact RamareSaouter2003.prime_interval_nat_ladder_c06253 n (by omega) (by omega)
            · -- n <= 107204941204112207
              exact RamareSaouter2003.prime_interval_nat_ladder_c06252 n (by omega) (by omega)
          · -- n <= 106902290121949957
            exact RamareSaouter2003.prime_interval_nat_ladder_c06251 n (by omega) (by omega)
