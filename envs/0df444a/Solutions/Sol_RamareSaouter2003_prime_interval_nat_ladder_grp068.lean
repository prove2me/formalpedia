-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T04:31:32.509282+00:00
-- url     : https://prove2.me/submissions/97e86524-7c37-4672-87ac-ac724e2582c0

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03400

theorem solution (n : Nat)
    (hn : 36042222348907 < n) (hupper : n <= 40783396349303) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 38339591017181 n with h2 | h2
  · -- n > 38339591017181
    rcases Nat.lt_or_ge 39493781092321 n with h4 | h4
    · -- n > 39493781092321
      rcases Nat.lt_or_ge 40083841302181 n with h6 | h6
      · -- n > 40083841302181
        rcases Nat.lt_or_ge 40382169162901 n with h8 | h8
        · -- n > 40382169162901
          rcases Nat.lt_or_ge 40582286904647 n with h10 | h10
          · -- n > 40582286904647
            rcases Nat.lt_or_ge 40682717357551 n with h12 | h12
            · -- n > 40682717357551
              exact RamareSaouter2003.prime_interval_nat_ladder_c03400 n (by omega) (by omega)
            · -- n <= 40682717357551
              exact RamareSaouter2003.prime_interval_nat_ladder_c03399 n (by omega) (by omega)
          · -- n <= 40582286904647
            rcases Nat.lt_or_ge 40482104377087 n with h12 | h12
            · -- n > 40482104377087
              exact RamareSaouter2003.prime_interval_nat_ladder_c03398 n (by omega) (by omega)
            · -- n <= 40482104377087
              exact RamareSaouter2003.prime_interval_nat_ladder_c03397 n (by omega) (by omega)
        · -- n <= 40382169162901
          rcases Nat.lt_or_ge 40183038233699 n with h10 | h10
          · -- n > 40183038233699
            rcases Nat.lt_or_ge 40282480651429 n with h12 | h12
            · -- n > 40282480651429
              exact RamareSaouter2003.prime_interval_nat_ladder_c03396 n (by omega) (by omega)
            · -- n <= 40282480651429
              exact RamareSaouter2003.prime_interval_nat_ladder_c03395 n (by omega) (by omega)
          · -- n <= 40183038233699
            exact RamareSaouter2003.prime_interval_nat_ladder_c03394 n (by omega) (by omega)
      · -- n <= 40083841302181
        rcases Nat.lt_or_ge 39787717372723 n with h8 | h8
        · -- n > 39787717372723
          rcases Nat.lt_or_ge 39886181475307 n with h10 | h10
          · -- n > 39886181475307
            rcases Nat.lt_or_ge 39984889250923 n with h12 | h12
            · -- n > 39984889250923
              exact RamareSaouter2003.prime_interval_nat_ladder_c03393 n (by omega) (by omega)
            · -- n <= 39984889250923
              exact RamareSaouter2003.prime_interval_nat_ladder_c03392 n (by omega) (by omega)
          · -- n <= 39886181475307
            exact RamareSaouter2003.prime_interval_nat_ladder_c03391 n (by omega) (by omega)
        · -- n <= 39787717372723
          rcases Nat.lt_or_ge 39591517780487 n with h10 | h10
          · -- n > 39591517780487
            rcases Nat.lt_or_ge 39689496341023 n with h12 | h12
            · -- n > 39689496341023
              exact RamareSaouter2003.prime_interval_nat_ladder_c03390 n (by omega) (by omega)
            · -- n <= 39689496341023
              exact RamareSaouter2003.prime_interval_nat_ladder_c03389 n (by omega) (by omega)
          · -- n <= 39591517780487
            exact RamareSaouter2003.prime_interval_nat_ladder_c03388 n (by omega) (by omega)
    · -- n <= 39493781092321
      rcases Nat.lt_or_ge 38912406952087 n with h6 | h6
      · -- n > 38912406952087
        rcases Nat.lt_or_ge 39202016299493 n with h8 | h8
        · -- n > 39202016299493
          rcases Nat.lt_or_ge 39299030946673 n with h10 | h10
          · -- n > 39299030946673
            rcases Nat.lt_or_ge 39396285679537 n with h12 | h12
            · -- n > 39396285679537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03387 n (by omega) (by omega)
            · -- n <= 39396285679537
              exact RamareSaouter2003.prime_interval_nat_ladder_c03386 n (by omega) (by omega)
          · -- n <= 39299030946673
            exact RamareSaouter2003.prime_interval_nat_ladder_c03385 n (by omega) (by omega)
        · -- n <= 39202016299493
          rcases Nat.lt_or_ge 39008704892701 n with h10 | h10
          · -- n > 39008704892701
            rcases Nat.lt_or_ge 39105241145233 n with h12 | h12
            · -- n > 39105241145233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03384 n (by omega) (by omega)
            · -- n <= 39105241145233
              exact RamareSaouter2003.prime_interval_nat_ladder_c03383 n (by omega) (by omega)
          · -- n <= 39008704892701
            exact RamareSaouter2003.prime_interval_nat_ladder_c03382 n (by omega) (by omega)
      · -- n <= 38912406952087
        rcases Nat.lt_or_ge 38624937126617 n with h8 | h8
        · -- n > 38624937126617
          rcases Nat.lt_or_ge 38720523655211 n with h10 | h10
          · -- n > 38720523655211
            rcases Nat.lt_or_ge 38816346735289 n with h12 | h12
            · -- n > 38816346735289
              exact RamareSaouter2003.prime_interval_nat_ladder_c03381 n (by omega) (by omega)
            · -- n <= 38816346735289
              exact RamareSaouter2003.prime_interval_nat_ladder_c03380 n (by omega) (by omega)
          · -- n <= 38720523655211
            exact RamareSaouter2003.prime_interval_nat_ladder_c03379 n (by omega) (by omega)
        · -- n <= 38624937126617
          rcases Nat.lt_or_ge 38434471389469 n with h10 | h10
          · -- n > 38434471389469
            rcases Nat.lt_or_ge 38529586565567 n with h12 | h12
            · -- n > 38529586565567
              exact RamareSaouter2003.prime_interval_nat_ladder_c03378 n (by omega) (by omega)
            · -- n <= 38529586565567
              exact RamareSaouter2003.prime_interval_nat_ladder_c03377 n (by omega) (by omega)
          · -- n <= 38434471389469
            exact RamareSaouter2003.prime_interval_nat_ladder_c03376 n (by omega) (by omega)
  · -- n <= 38339591017181
    rcases Nat.lt_or_ge 37127251537309 n with h4 | h4
    · -- n > 37127251537309
      rcases Nat.lt_or_ge 37681954410407 n with h6 | h6
      · -- n > 37681954410407
        rcases Nat.lt_or_ge 37962405995963 n with h8 | h8
        · -- n > 37962405995963
          rcases Nat.lt_or_ge 38150532367231 n with h10 | h10
          · -- n > 38150532367231
            rcases Nat.lt_or_ge 38244944869213 n with h12 | h12
            · -- n > 38244944869213
              exact RamareSaouter2003.prime_interval_nat_ladder_c03375 n (by omega) (by omega)
            · -- n <= 38244944869213
              exact RamareSaouter2003.prime_interval_nat_ladder_c03374 n (by omega) (by omega)
          · -- n <= 38150532367231
            rcases Nat.lt_or_ge 38056352934781 n with h12 | h12
            · -- n > 38056352934781
              exact RamareSaouter2003.prime_interval_nat_ladder_c03373 n (by omega) (by omega)
            · -- n <= 38056352934781
              exact RamareSaouter2003.prime_interval_nat_ladder_c03372 n (by omega) (by omega)
        · -- n <= 37962405995963
          rcases Nat.lt_or_ge 37775207305597 n with h10 | h10
          · -- n > 37775207305597
            rcases Nat.lt_or_ge 37868690977087 n with h12 | h12
            · -- n > 37868690977087
              exact RamareSaouter2003.prime_interval_nat_ladder_c03371 n (by omega) (by omega)
            · -- n <= 37868690977087
              exact RamareSaouter2003.prime_interval_nat_ladder_c03370 n (by omega) (by omega)
          · -- n <= 37775207305597
            exact RamareSaouter2003.prime_interval_nat_ladder_c03369 n (by omega) (by omega)
      · -- n <= 37681954410407
        rcases Nat.lt_or_ge 37403574692863 n with h8 | h8
        · -- n > 37403574692863
          rcases Nat.lt_or_ge 37496138671577 n with h10 | h10
          · -- n > 37496138671577
            rcases Nat.lt_or_ge 37588931721857 n with h12 | h12
            · -- n > 37588931721857
              exact RamareSaouter2003.prime_interval_nat_ladder_c03368 n (by omega) (by omega)
            · -- n <= 37588931721857
              exact RamareSaouter2003.prime_interval_nat_ladder_c03367 n (by omega) (by omega)
          · -- n <= 37496138671577
            exact RamareSaouter2003.prime_interval_nat_ladder_c03366 n (by omega) (by omega)
        · -- n <= 37403574692863
          rcases Nat.lt_or_ge 37219131689101 n with h10 | h10
          · -- n > 37219131689101
            rcases Nat.lt_or_ge 37311239219963 n with h12 | h12
            · -- n > 37311239219963
              exact RamareSaouter2003.prime_interval_nat_ladder_c03365 n (by omega) (by omega)
            · -- n <= 37311239219963
              exact RamareSaouter2003.prime_interval_nat_ladder_c03364 n (by omega) (by omega)
          · -- n <= 37219131689101
            exact RamareSaouter2003.prime_interval_nat_ladder_c03363 n (by omega) (by omega)
    · -- n <= 37127251537309
      rcases Nat.lt_or_ge 36580714251013 n with h6 | h6
      · -- n > 36580714251013
        rcases Nat.lt_or_ge 36852969750097 n with h8 | h8
        · -- n > 36852969750097
          rcases Nat.lt_or_ge 36944171126983 n with h10 | h10
          · -- n > 36944171126983
            rcases Nat.lt_or_ge 37035598203193 n with h12 | h12
            · -- n > 37035598203193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03362 n (by omega) (by omega)
            · -- n <= 37035598203193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03361 n (by omega) (by omega)
          · -- n <= 36944171126983
            exact RamareSaouter2003.prime_interval_nat_ladder_c03360 n (by omega) (by omega)
        · -- n <= 36852969750097
          rcases Nat.lt_or_ge 36671241867319 n with h10 | h10
          · -- n > 36671241867319
            rcases Nat.lt_or_ge 36761993515631 n with h12 | h12
            · -- n > 36761993515631
              exact RamareSaouter2003.prime_interval_nat_ladder_c03359 n (by omega) (by omega)
            · -- n <= 36761993515631
              exact RamareSaouter2003.prime_interval_nat_ladder_c03358 n (by omega) (by omega)
          · -- n <= 36671241867319
            exact RamareSaouter2003.prime_interval_nat_ladder_c03357 n (by omega) (by omega)
      · -- n <= 36580714251013
        rcases Nat.lt_or_ge 36310470070111 n with h8 | h8
        · -- n > 36310470070111
          rcases Nat.lt_or_ge 36400328903417 n with h10 | h10
          · -- n > 36400328903417
            rcases Nat.lt_or_ge 36490410113569 n with h12 | h12
            · -- n > 36490410113569
              exact RamareSaouter2003.prime_interval_nat_ladder_c03356 n (by omega) (by omega)
            · -- n <= 36490410113569
              exact RamareSaouter2003.prime_interval_nat_ladder_c03355 n (by omega) (by omega)
          · -- n <= 36400328903417
            exact RamareSaouter2003.prime_interval_nat_ladder_c03354 n (by omega) (by omega)
        · -- n <= 36310470070111
          rcases Nat.lt_or_ge 36131417339839 n with h10 | h10
          · -- n > 36131417339839
            rcases Nat.lt_or_ge 36220833064811 n with h12 | h12
            · -- n > 36220833064811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03353 n (by omega) (by omega)
            · -- n <= 36220833064811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03352 n (by omega) (by omega)
          · -- n <= 36131417339839
            exact RamareSaouter2003.prime_interval_nat_ladder_c03351 n (by omega) (by omega)
