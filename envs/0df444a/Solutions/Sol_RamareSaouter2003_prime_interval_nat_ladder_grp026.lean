-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T05:38:05.390846+00:00
-- url     : https://prove2.me/submissions/f05468b3-2eaa-4d9a-b64b-cb167ebc8764

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01300

theorem solution (n : Nat)
    (hn : 189054413519 < n) (hupper : n <= 214261267621) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 201259941457 n with h2 | h2
  · -- n > 201259941457
    rcases Nat.lt_or_ge 207398115667 n with h4 | h4
    · -- n > 207398115667
      rcases Nat.lt_or_ge 210537714581 n with h6 | h6
      · -- n > 210537714581
        rcases Nat.lt_or_ge 212125458893 n with h8 | h8
        · -- n > 212125458893
          rcases Nat.lt_or_ge 213190663793 n with h10 | h10
          · -- n > 213190663793
            rcases Nat.lt_or_ge 213725289103 n with h12 | h12
            · -- n > 213725289103
              exact RamareSaouter2003.prime_interval_nat_ladder_c01300 n (by omega) (by omega)
            · -- n <= 213725289103
              exact RamareSaouter2003.prime_interval_nat_ladder_c01299 n (by omega) (by omega)
          · -- n <= 213190663793
            rcases Nat.lt_or_ge 212657388199 n with h12 | h12
            · -- n > 212657388199
              exact RamareSaouter2003.prime_interval_nat_ladder_c01298 n (by omega) (by omega)
            · -- n <= 212657388199
              exact RamareSaouter2003.prime_interval_nat_ladder_c01297 n (by omega) (by omega)
        · -- n <= 212125458893
          rcases Nat.lt_or_ge 211065625549 n with h10 | h10
          · -- n > 211065625549
            rcases Nat.lt_or_ge 211594872539 n with h12 | h12
            · -- n > 211594872539
              exact RamareSaouter2003.prime_interval_nat_ladder_c01296 n (by omega) (by omega)
            · -- n <= 211594872539
              exact RamareSaouter2003.prime_interval_nat_ladder_c01295 n (by omega) (by omega)
          · -- n <= 211065625549
            exact RamareSaouter2003.prime_interval_nat_ladder_c01294 n (by omega) (by omega)
      · -- n <= 210537714581
        rcases Nat.lt_or_ge 208961963983 n with h8 | h8
        · -- n > 208961963983
          rcases Nat.lt_or_ge 209485887241 n with h10 | h10
          · -- n > 209485887241
            rcases Nat.lt_or_ge 210011136289 n with h12 | h12
            · -- n > 210011136289
              exact RamareSaouter2003.prime_interval_nat_ladder_c01293 n (by omega) (by omega)
            · -- n <= 210011136289
              exact RamareSaouter2003.prime_interval_nat_ladder_c01292 n (by omega) (by omega)
          · -- n <= 209485887241
            exact RamareSaouter2003.prime_interval_nat_ladder_c01291 n (by omega) (by omega)
        · -- n <= 208961963983
          rcases Nat.lt_or_ge 207918081577 n with h10 | h10
          · -- n > 207918081577
            rcases Nat.lt_or_ge 208439363203 n with h12 | h12
            · -- n > 208439363203
              exact RamareSaouter2003.prime_interval_nat_ladder_c01290 n (by omega) (by omega)
            · -- n <= 208439363203
              exact RamareSaouter2003.prime_interval_nat_ladder_c01289 n (by omega) (by omega)
          · -- n <= 207918081577
            exact RamareSaouter2003.prime_interval_nat_ladder_c01288 n (by omega) (by omega)
    · -- n <= 207398115667
      rcases Nat.lt_or_ge 204305763691 n with h6 | h6
      · -- n > 204305763691
        rcases Nat.lt_or_ge 205846078897 n with h8 | h8
        · -- n > 205846078897
          rcases Nat.lt_or_ge 206362117651 n with h10 | h10
          · -- n > 206362117651
            rcases Nat.lt_or_ge 206879462137 n with h12 | h12
            · -- n > 206879462137
              exact RamareSaouter2003.prime_interval_nat_ladder_c01287 n (by omega) (by omega)
            · -- n <= 206879462137
              exact RamareSaouter2003.prime_interval_nat_ladder_c01286 n (by omega) (by omega)
          · -- n <= 206362117651
            exact RamareSaouter2003.prime_interval_nat_ladder_c01285 n (by omega) (by omega)
        · -- n <= 205846078897
          rcases Nat.lt_or_ge 204817905209 n with h10 | h10
          · -- n > 204817905209
            rcases Nat.lt_or_ge 205331342519 n with h12 | h12
            · -- n > 205331342519
              exact RamareSaouter2003.prime_interval_nat_ladder_c01284 n (by omega) (by omega)
            · -- n <= 205331342519
              exact RamareSaouter2003.prime_interval_nat_ladder_c01283 n (by omega) (by omega)
          · -- n <= 204817905209
            exact RamareSaouter2003.prime_interval_nat_ladder_c01282 n (by omega) (by omega)
      · -- n <= 204305763691
        rcases Nat.lt_or_ge 202777080739 n with h8 | h8
        · -- n > 202777080739
          rcases Nat.lt_or_ge 203285354761 n with h10 | h10
          · -- n > 203285354761
            rcases Nat.lt_or_ge 203794914667 n with h12 | h12
            · -- n > 203794914667
              exact RamareSaouter2003.prime_interval_nat_ladder_c01281 n (by omega) (by omega)
            · -- n <= 203794914667
              exact RamareSaouter2003.prime_interval_nat_ladder_c01280 n (by omega) (by omega)
          · -- n <= 203285354761
            exact RamareSaouter2003.prime_interval_nat_ladder_c01279 n (by omega) (by omega)
        · -- n <= 202777080739
          rcases Nat.lt_or_ge 201764377357 n with h10 | h10
          · -- n > 201764377357
            rcases Nat.lt_or_ge 202270089391 n with h12 | h12
            · -- n > 202270089391
              exact RamareSaouter2003.prime_interval_nat_ladder_c01278 n (by omega) (by omega)
            · -- n <= 202270089391
              exact RamareSaouter2003.prime_interval_nat_ladder_c01277 n (by omega) (by omega)
          · -- n <= 201764377357
            exact RamareSaouter2003.prime_interval_nat_ladder_c01276 n (by omega) (by omega)
  · -- n <= 201259941457
    rcases Nat.lt_or_ge 194816931391 n with h4 | h4
    · -- n > 194816931391
      rcases Nat.lt_or_ge 197764348493 n with h6 | h6
      · -- n > 197764348493
        rcases Nat.lt_or_ge 199254893707 n with h8 | h8
        · -- n > 199254893707
          rcases Nat.lt_or_ge 200254884847 n with h10 | h10
          · -- n > 200254884847
            rcases Nat.lt_or_ge 200756778367 n with h12 | h12
            · -- n > 200756778367
              exact RamareSaouter2003.prime_interval_nat_ladder_c01275 n (by omega) (by omega)
            · -- n <= 200756778367
              exact RamareSaouter2003.prime_interval_nat_ladder_c01274 n (by omega) (by omega)
          · -- n <= 200254884847
            rcases Nat.lt_or_ge 199754257711 n with h12 | h12
            · -- n > 199754257711
              exact RamareSaouter2003.prime_interval_nat_ladder_c01273 n (by omega) (by omega)
            · -- n <= 199754257711
              exact RamareSaouter2003.prime_interval_nat_ladder_c01272 n (by omega) (by omega)
        · -- n <= 199254893707
          rcases Nat.lt_or_ge 198259942301 n with h10 | h10
          · -- n > 198259942301
            rcases Nat.lt_or_ge 198756789643 n with h12 | h12
            · -- n > 198756789643
              exact RamareSaouter2003.prime_interval_nat_ladder_c01271 n (by omega) (by omega)
            · -- n <= 198756789643
              exact RamareSaouter2003.prime_interval_nat_ladder_c01270 n (by omega) (by omega)
          · -- n <= 198259942301
            exact RamareSaouter2003.prime_interval_nat_ladder_c01269 n (by omega) (by omega)
      · -- n <= 197764348493
        rcases Nat.lt_or_ge 196285056307 n with h8 | h8
        · -- n > 196285056307
          rcases Nat.lt_or_ge 196776908689 n with h10 | h10
          · -- n > 196776908689
            rcases Nat.lt_or_ge 197270005027 n with h12 | h12
            · -- n > 197270005027
              exact RamareSaouter2003.prime_interval_nat_ladder_c01268 n (by omega) (by omega)
            · -- n <= 197270005027
              exact RamareSaouter2003.prime_interval_nat_ladder_c01267 n (by omega) (by omega)
          · -- n <= 196776908689
            exact RamareSaouter2003.prime_interval_nat_ladder_c01266 n (by omega) (by omega)
        · -- n <= 196285056307
          rcases Nat.lt_or_ge 195305070823 n with h10 | h10
          · -- n > 195305070823
            rcases Nat.lt_or_ge 195794444737 n with h12 | h12
            · -- n > 195794444737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01265 n (by omega) (by omega)
            · -- n <= 195794444737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01264 n (by omega) (by omega)
          · -- n <= 195305070823
            exact RamareSaouter2003.prime_interval_nat_ladder_c01263 n (by omega) (by omega)
    · -- n <= 194816931391
      rcases Nat.lt_or_ge 191913844049 n with h6 | h6
      · -- n > 191913844049
        rcases Nat.lt_or_ge 193359888811 n with h8 | h8
        · -- n > 193359888811
          rcases Nat.lt_or_ge 193844343461 n with h10 | h10
          · -- n > 193844343461
            rcases Nat.lt_or_ge 194330023319 n with h12 | h12
            · -- n > 194330023319
              exact RamareSaouter2003.prime_interval_nat_ladder_c01262 n (by omega) (by omega)
            · -- n <= 194330023319
              exact RamareSaouter2003.prime_interval_nat_ladder_c01261 n (by omega) (by omega)
          · -- n <= 193844343461
            exact RamareSaouter2003.prime_interval_nat_ladder_c01260 n (by omega) (by omega)
        · -- n <= 193359888811
          rcases Nat.lt_or_ge 192394642093 n with h10 | h10
          · -- n > 192394642093
            rcases Nat.lt_or_ge 192876656023 n with h12 | h12
            · -- n > 192876656023
              exact RamareSaouter2003.prime_interval_nat_ladder_c01259 n (by omega) (by omega)
            · -- n <= 192876656023
              exact RamareSaouter2003.prime_interval_nat_ladder_c01258 n (by omega) (by omega)
          · -- n <= 192394642093
            exact RamareSaouter2003.prime_interval_nat_ladder_c01257 n (by omega) (by omega)
      · -- n <= 191913844049
        rcases Nat.lt_or_ge 190478713319 n with h8 | h8
        · -- n > 190478713319
          rcases Nat.lt_or_ge 190955882707 n with h10 | h10
          · -- n > 190955882707
            rcases Nat.lt_or_ge 191434258549 n with h12 | h12
            · -- n > 191434258549
              exact RamareSaouter2003.prime_interval_nat_ladder_c01256 n (by omega) (by omega)
            · -- n <= 191434258549
              exact RamareSaouter2003.prime_interval_nat_ladder_c01255 n (by omega) (by omega)
          · -- n <= 190955882707
            exact RamareSaouter2003.prime_interval_nat_ladder_c01254 n (by omega) (by omega)
        · -- n <= 190478713319
          rcases Nat.lt_or_ge 189527981827 n with h10 | h10
          · -- n > 189527981827
            rcases Nat.lt_or_ge 190002747371 n with h12 | h12
            · -- n > 190002747371
              exact RamareSaouter2003.prime_interval_nat_ladder_c01253 n (by omega) (by omega)
            · -- n <= 190002747371
              exact RamareSaouter2003.prime_interval_nat_ladder_c01252 n (by omega) (by omega)
          · -- n <= 189527981827
            exact RamareSaouter2003.prime_interval_nat_ladder_c01251 n (by omega) (by omega)
