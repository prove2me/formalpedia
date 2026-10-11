-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T16:52:26.303719+00:00
-- url     : https://prove2.me/submissions/660bb15b-ec1e-4f22-8ed6-b1f0aca0b12c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00300

theorem solution (n : Nat)
    (hn : 18481081387 < n) (hupper : n <= 20638678393) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 19528776587 n with h2 | h2
  · -- n > 19528776587
    rcases Nat.lt_or_ge 20053534289 n with h4 | h4
    · -- n > 20053534289
      rcases Nat.lt_or_ge 20321417107 n with h6 | h6
      · -- n > 20321417107
        rcases Nat.lt_or_ge 20456757823 n with h8 | h8
        · -- n > 20456757823
          rcases Nat.lt_or_ge 20547507821 n with h10 | h10
          · -- n > 20547507821
            rcases Nat.lt_or_ge 20593040387 n with h12 | h12
            · -- n > 20593040387
              exact RamareSaouter2003.prime_interval_nat_ladder_c00300 n (by omega) (by omega)
            · -- n <= 20593040387
              exact RamareSaouter2003.prime_interval_nat_ladder_c00299 n (by omega) (by omega)
          · -- n <= 20547507821
            rcases Nat.lt_or_ge 20502080369 n with h12 | h12
            · -- n > 20502080369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00298 n (by omega) (by omega)
            · -- n <= 20502080369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00297 n (by omega) (by omega)
        · -- n <= 20456757823
          rcases Nat.lt_or_ge 20366426453 n with h10 | h10
          · -- n > 20366426453
            rcases Nat.lt_or_ge 20411539933 n with h12 | h12
            · -- n > 20411539933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00296 n (by omega) (by omega)
            · -- n <= 20411539933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00295 n (by omega) (by omega)
          · -- n <= 20366426453
            exact RamareSaouter2003.prime_interval_nat_ladder_c00294 n (by omega) (by omega)
      · -- n <= 20321417107
        rcases Nat.lt_or_ge 20187011549 n with h8 | h8
        · -- n > 20187011549
          rcases Nat.lt_or_ge 20231709929 n with h10 | h10
          · -- n > 20231709929
            rcases Nat.lt_or_ge 20276511737 n with h12 | h12
            · -- n > 20276511737
              exact RamareSaouter2003.prime_interval_nat_ladder_c00293 n (by omega) (by omega)
            · -- n <= 20276511737
              exact RamareSaouter2003.prime_interval_nat_ladder_c00292 n (by omega) (by omega)
          · -- n <= 20231709929
            exact RamareSaouter2003.prime_interval_nat_ladder_c00291 n (by omega) (by omega)
        · -- n <= 20187011549
          rcases Nat.lt_or_ge 20097923981 n with h10 | h10
          · -- n > 20097923981
            rcases Nat.lt_or_ge 20142416321 n with h12 | h12
            · -- n > 20142416321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00290 n (by omega) (by omega)
            · -- n <= 20142416321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00289 n (by omega) (by omega)
          · -- n <= 20097923981
            exact RamareSaouter2003.prime_interval_nat_ladder_c00288 n (by omega) (by omega)
    · -- n <= 20053534289
      rcases Nat.lt_or_ge 19789338433 n with h6 | h6
      · -- n > 19789338433
        rcases Nat.lt_or_ge 19920978809 n with h8 | h8
        · -- n > 19920978809
          rcases Nat.lt_or_ge 19965061993 n with h10 | h10
          · -- n > 19965061993
            rcases Nat.lt_or_ge 20009247047 n with h12 | h12
            · -- n > 20009247047
              exact RamareSaouter2003.prime_interval_nat_ladder_c00287 n (by omega) (by omega)
            · -- n <= 20009247047
              exact RamareSaouter2003.prime_interval_nat_ladder_c00286 n (by omega) (by omega)
          · -- n <= 19965061993
            exact RamareSaouter2003.prime_interval_nat_ladder_c00285 n (by omega) (by omega)
        · -- n <= 19920978809
          rcases Nat.lt_or_ge 19833117307 n with h10 | h10
          · -- n > 19833117307
            rcases Nat.lt_or_ge 19876997297 n with h12 | h12
            · -- n > 19876997297
              exact RamareSaouter2003.prime_interval_nat_ladder_c00284 n (by omega) (by omega)
            · -- n <= 19876997297
              exact RamareSaouter2003.prime_interval_nat_ladder_c00283 n (by omega) (by omega)
          · -- n <= 19833117307
            exact RamareSaouter2003.prime_interval_nat_ladder_c00282 n (by omega) (by omega)
      · -- n <= 19789338433
        rcases Nat.lt_or_ge 19658606551 n with h8 | h8
        · -- n > 19658606551
          rcases Nat.lt_or_ge 19702083259 n with h10 | h10
          · -- n > 19702083259
            rcases Nat.lt_or_ge 19745660509 n with h12 | h12
            · -- n > 19745660509
              exact RamareSaouter2003.prime_interval_nat_ladder_c00281 n (by omega) (by omega)
            · -- n <= 19745660509
              exact RamareSaouter2003.prime_interval_nat_ladder_c00280 n (by omega) (by omega)
          · -- n <= 19702083259
            exact RamareSaouter2003.prime_interval_nat_ladder_c00279 n (by omega) (by omega)
        · -- n <= 19658606551
          rcases Nat.lt_or_ge 19571953439 n with h10 | h10
          · -- n > 19571953439
            rcases Nat.lt_or_ge 19615229983 n with h12 | h12
            · -- n > 19615229983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00278 n (by omega) (by omega)
            · -- n <= 19615229983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00277 n (by omega) (by omega)
          · -- n <= 19571953439
            exact RamareSaouter2003.prime_interval_nat_ladder_c00276 n (by omega) (by omega)
  · -- n <= 19528776587
    rcases Nat.lt_or_ge 18976445881 n with h4 | h4
    · -- n > 18976445881
      rcases Nat.lt_or_ge 19229311379 n with h6 | h6
      · -- n > 19229311379
        rcases Nat.lt_or_ge 19357061797 n with h8 | h8
        · -- n > 19357061797
          rcases Nat.lt_or_ge 19442721157 n with h10 | h10
          · -- n > 19442721157
            rcases Nat.lt_or_ge 19485699229 n with h12 | h12
            · -- n > 19485699229
              exact RamareSaouter2003.prime_interval_nat_ladder_c00275 n (by omega) (by omega)
            · -- n <= 19485699229
              exact RamareSaouter2003.prime_interval_nat_ladder_c00274 n (by omega) (by omega)
          · -- n <= 19442721157
            rcases Nat.lt_or_ge 19399842083 n with h12 | h12
            · -- n > 19399842083
              exact RamareSaouter2003.prime_interval_nat_ladder_c00273 n (by omega) (by omega)
            · -- n <= 19399842083
              exact RamareSaouter2003.prime_interval_nat_ladder_c00272 n (by omega) (by omega)
        · -- n <= 19357061797
          rcases Nat.lt_or_ge 19271796721 n with h10 | h10
          · -- n > 19271796721
            rcases Nat.lt_or_ge 19314380131 n with h12 | h12
            · -- n > 19314380131
              exact RamareSaouter2003.prime_interval_nat_ladder_c00271 n (by omega) (by omega)
            · -- n <= 19314380131
              exact RamareSaouter2003.prime_interval_nat_ladder_c00270 n (by omega) (by omega)
          · -- n <= 19271796721
            exact RamareSaouter2003.prime_interval_nat_ladder_c00269 n (by omega) (by omega)
      · -- n <= 19229311379
        rcases Nat.lt_or_ge 19102441447 n with h8 | h8
        · -- n > 19102441447
          rcases Nat.lt_or_ge 19144633973 n with h10 | h10
          · -- n > 19144633973
            rcases Nat.lt_or_ge 19186923869 n with h12 | h12
            · -- n > 19186923869
              exact RamareSaouter2003.prime_interval_nat_ladder_c00268 n (by omega) (by omega)
            · -- n <= 19186923869
              exact RamareSaouter2003.prime_interval_nat_ladder_c00267 n (by omega) (by omega)
          · -- n <= 19144633973
            exact RamareSaouter2003.prime_interval_nat_ladder_c00266 n (by omega) (by omega)
        · -- n <= 19102441447
          rcases Nat.lt_or_ge 19018347683 n with h10 | h10
          · -- n > 19018347683
            rcases Nat.lt_or_ge 19060346159 n with h12 | h12
            · -- n > 19060346159
              exact RamareSaouter2003.prime_interval_nat_ladder_c00265 n (by omega) (by omega)
            · -- n <= 19060346159
              exact RamareSaouter2003.prime_interval_nat_ladder_c00264 n (by omega) (by omega)
          · -- n <= 19018347683
            exact RamareSaouter2003.prime_interval_nat_ladder_c00263 n (by omega) (by omega)
    · -- n <= 18976445881
      rcases Nat.lt_or_ge 18727052467 n with h6 | h6
      · -- n > 18727052467
        rcases Nat.lt_or_ge 18851318257 n with h8 | h8
        · -- n > 18851318257
          rcases Nat.lt_or_ge 18892931411 n with h10 | h10
          · -- n > 18892931411
            rcases Nat.lt_or_ge 18934640537 n with h12 | h12
            · -- n > 18934640537
              exact RamareSaouter2003.prime_interval_nat_ladder_c00262 n (by omega) (by omega)
            · -- n <= 18934640537
              exact RamareSaouter2003.prime_interval_nat_ladder_c00261 n (by omega) (by omega)
          · -- n <= 18892931411
            exact RamareSaouter2003.prime_interval_nat_ladder_c00260 n (by omega) (by omega)
        · -- n <= 18851318257
          rcases Nat.lt_or_ge 18768378997 n with h10 | h10
          · -- n > 18768378997
            rcases Nat.lt_or_ge 18809800897 n with h12 | h12
            · -- n > 18809800897
              exact RamareSaouter2003.prime_interval_nat_ladder_c00259 n (by omega) (by omega)
            · -- n <= 18809800897
              exact RamareSaouter2003.prime_interval_nat_ladder_c00258 n (by omega) (by omega)
          · -- n <= 18768378997
            exact RamareSaouter2003.prime_interval_nat_ladder_c00257 n (by omega) (by omega)
      · -- n <= 18727052467
        rcases Nat.lt_or_ge 18603642227 n with h8 | h8
        · -- n > 18603642227
          rcases Nat.lt_or_ge 18644684257 n with h10 | h10
          · -- n > 18644684257
            rcases Nat.lt_or_ge 18685820957 n with h12 | h12
            · -- n > 18685820957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00256 n (by omega) (by omega)
            · -- n <= 18685820957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00255 n (by omega) (by omega)
          · -- n <= 18644684257
            exact RamareSaouter2003.prime_interval_nat_ladder_c00254 n (by omega) (by omega)
        · -- n <= 18603642227
          rcases Nat.lt_or_ge 18521840983 n with h10 | h10
          · -- n > 18521840983
            rcases Nat.lt_or_ge 18562694533 n with h12 | h12
            · -- n > 18562694533
              exact RamareSaouter2003.prime_interval_nat_ladder_c00253 n (by omega) (by omega)
            · -- n <= 18562694533
              exact RamareSaouter2003.prime_interval_nat_ladder_c00252 n (by omega) (by omega)
          · -- n <= 18521840983
            exact RamareSaouter2003.prime_interval_nat_ladder_c00251 n (by omega) (by omega)
