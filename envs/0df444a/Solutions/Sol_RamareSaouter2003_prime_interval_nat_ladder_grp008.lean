-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T18:07:13.358971+00:00
-- url     : https://prove2.me/submissions/99a0bb84-8a88-4b73-8c85-d453df53ba43

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00400

theorem solution (n : Nat)
    (hn : 23060765993 < n) (hupper : n <= 25781257687) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 24381421501 n with h2 | h2
  · -- n > 24381421501
    rcases Nat.lt_or_ge 25043163517 n with h4 | h4
    · -- n > 25043163517
      rcases Nat.lt_or_ge 25381041739 n with h6 | h6
      · -- n > 25381041739
        rcases Nat.lt_or_ge 25551762631 n with h8 | h8
        · -- n > 25551762631
          rcases Nat.lt_or_ge 25666242367 n with h10 | h10
          · -- n > 25666242367
            rcases Nat.lt_or_ge 25723682909 n with h12 | h12
            · -- n > 25723682909
              exact RamareSaouter2003.prime_interval_nat_ladder_c00400 n (by omega) (by omega)
            · -- n <= 25723682909
              exact RamareSaouter2003.prime_interval_nat_ladder_c00399 n (by omega) (by omega)
          · -- n <= 25666242367
            rcases Nat.lt_or_ge 25608935717 n with h12 | h12
            · -- n > 25608935717
              exact RamareSaouter2003.prime_interval_nat_ladder_c00398 n (by omega) (by omega)
            · -- n <= 25608935717
              exact RamareSaouter2003.prime_interval_nat_ladder_c00397 n (by omega) (by omega)
        · -- n <= 25551762631
          rcases Nat.lt_or_ge 25437815983 n with h10 | h10
          · -- n > 25437815983
            rcases Nat.lt_or_ge 25494722821 n with h12 | h12
            · -- n > 25494722821
              exact RamareSaouter2003.prime_interval_nat_ladder_c00396 n (by omega) (by omega)
            · -- n <= 25494722821
              exact RamareSaouter2003.prime_interval_nat_ladder_c00395 n (by omega) (by omega)
          · -- n <= 25437815983
            exact RamareSaouter2003.prime_interval_nat_ladder_c00394 n (by omega) (by omega)
      · -- n <= 25381041739
        rcases Nat.lt_or_ge 25211511557 n with h8 | h8
        · -- n > 25211511557
          rcases Nat.lt_or_ge 25267889849 n with h10 | h10
          · -- n > 25267889849
            rcases Nat.lt_or_ge 25324399801 n with h12 | h12
            · -- n > 25324399801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00393 n (by omega) (by omega)
            · -- n <= 25324399801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00392 n (by omega) (by omega)
          · -- n <= 25267889849
            exact RamareSaouter2003.prime_interval_nat_ladder_c00391 n (by omega) (by omega)
        · -- n <= 25211511557
          rcases Nat.lt_or_ge 25099148663 n with h10 | h10
          · -- n > 25099148663
            rcases Nat.lt_or_ge 25155264587 n with h12 | h12
            · -- n > 25155264587
              exact RamareSaouter2003.prime_interval_nat_ladder_c00390 n (by omega) (by omega)
            · -- n <= 25155264587
              exact RamareSaouter2003.prime_interval_nat_ladder_c00389 n (by omega) (by omega)
          · -- n <= 25099148663
            exact RamareSaouter2003.prime_interval_nat_ladder_c00388 n (by omega) (by omega)
    · -- n <= 25043163517
      rcases Nat.lt_or_ge 24709979353 n with h6 | h6
      · -- n > 24709979353
        rcases Nat.lt_or_ge 24875988961 n with h8 | h8
        · -- n > 24875988961
          rcases Nat.lt_or_ge 24931583927 n with h10 | h10
          · -- n > 24931583927
            rcases Nat.lt_or_ge 24987308663 n with h12 | h12
            · -- n > 24987308663
              exact RamareSaouter2003.prime_interval_nat_ladder_c00387 n (by omega) (by omega)
            · -- n <= 24987308663
              exact RamareSaouter2003.prime_interval_nat_ladder_c00386 n (by omega) (by omega)
          · -- n <= 24931583927
            exact RamareSaouter2003.prime_interval_nat_ladder_c00385 n (by omega) (by omega)
        · -- n <= 24875988961
          rcases Nat.lt_or_ge 24765186977 n with h10 | h10
          · -- n > 24765186977
            rcases Nat.lt_or_ge 24820523423 n with h12 | h12
            · -- n > 24820523423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00384 n (by omega) (by omega)
            · -- n <= 24820523423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00383 n (by omega) (by omega)
          · -- n <= 24765186977
            exact RamareSaouter2003.prime_interval_nat_ladder_c00382 n (by omega) (by omega)
      · -- n <= 24709979353
        rcases Nat.lt_or_ge 24545126363 n with h8 | h8
        · -- n > 24545126363
          rcases Nat.lt_or_ge 24599949377 n with h10 | h10
          · -- n > 24599949377
            rcases Nat.lt_or_ge 24654900269 n with h12 | h12
            · -- n > 24654900269
              exact RamareSaouter2003.prime_interval_nat_ladder_c00381 n (by omega) (by omega)
            · -- n <= 24654900269
              exact RamareSaouter2003.prime_interval_nat_ladder_c00380 n (by omega) (by omega)
          · -- n <= 24599949377
            exact RamareSaouter2003.prime_interval_nat_ladder_c00379 n (by omega) (by omega)
        · -- n <= 24545126363
          rcases Nat.lt_or_ge 24435862739 n with h10 | h10
          · -- n > 24435862739
            rcases Nat.lt_or_ge 24490430963 n with h12 | h12
            · -- n > 24490430963
              exact RamareSaouter2003.prime_interval_nat_ladder_c00378 n (by omega) (by omega)
            · -- n <= 24490430963
              exact RamareSaouter2003.prime_interval_nat_ladder_c00377 n (by omega) (by omega)
          · -- n <= 24435862739
            exact RamareSaouter2003.prime_interval_nat_ladder_c00376 n (by omega) (by omega)
  · -- n <= 24381421501
    rcases Nat.lt_or_ge 23685099761 n with h4 | h4
    · -- n > 23685099761
      rcases Nat.lt_or_ge 24003861997 n with h6 | h6
      · -- n > 24003861997
        rcases Nat.lt_or_ge 24164920099 n with h8 | h8
        · -- n > 24164920099
          rcases Nat.lt_or_ge 24272918743 n with h10 | h10
          · -- n > 24272918743
            rcases Nat.lt_or_ge 24327106961 n with h12 | h12
            · -- n > 24327106961
              exact RamareSaouter2003.prime_interval_nat_ladder_c00375 n (by omega) (by omega)
            · -- n <= 24327106961
              exact RamareSaouter2003.prime_interval_nat_ladder_c00374 n (by omega) (by omega)
          · -- n <= 24272918743
            rcases Nat.lt_or_ge 24218856553 n with h12 | h12
            · -- n > 24218856553
              exact RamareSaouter2003.prime_interval_nat_ladder_c00373 n (by omega) (by omega)
            · -- n <= 24218856553
              exact RamareSaouter2003.prime_interval_nat_ladder_c00372 n (by omega) (by omega)
        · -- n <= 24164920099
          rcases Nat.lt_or_ge 24057423107 n with h10 | h10
          · -- n > 24057423107
            rcases Nat.lt_or_ge 24111109021 n with h12 | h12
            · -- n > 24111109021
              exact RamareSaouter2003.prime_interval_nat_ladder_c00371 n (by omega) (by omega)
            · -- n <= 24111109021
              exact RamareSaouter2003.prime_interval_nat_ladder_c00370 n (by omega) (by omega)
          · -- n <= 24057423107
            exact RamareSaouter2003.prime_interval_nat_ladder_c00369 n (by omega) (by omega)
      · -- n <= 24003861997
        rcases Nat.lt_or_ge 23843924551 n with h8 | h8
        · -- n > 23843924551
          rcases Nat.lt_or_ge 23897112983 n with h10 | h10
          · -- n > 23897112983
            rcases Nat.lt_or_ge 23950425379 n with h12 | h12
            · -- n > 23950425379
              exact RamareSaouter2003.prime_interval_nat_ladder_c00368 n (by omega) (by omega)
            · -- n <= 23950425379
              exact RamareSaouter2003.prime_interval_nat_ladder_c00367 n (by omega) (by omega)
          · -- n <= 23897112983
            exact RamareSaouter2003.prime_interval_nat_ladder_c00366 n (by omega) (by omega)
        · -- n <= 23843924551
          rcases Nat.lt_or_ge 23737918231 n with h10 | h10
          · -- n > 23737918231
            rcases Nat.lt_or_ge 23790859769 n with h12 | h12
            · -- n > 23790859769
              exact RamareSaouter2003.prime_interval_nat_ladder_c00365 n (by omega) (by omega)
            · -- n <= 23790859769
              exact RamareSaouter2003.prime_interval_nat_ladder_c00364 n (by omega) (by omega)
          · -- n <= 23737918231
            exact RamareSaouter2003.prime_interval_nat_ladder_c00363 n (by omega) (by omega)
    · -- n <= 23685099761
      rcases Nat.lt_or_ge 23370755783 n with h6 | h6
      · -- n > 23370755783
        rcases Nat.lt_or_ge 23527379479 n with h8 | h8
        · -- n > 23527379479
          rcases Nat.lt_or_ge 23579830649 n with h10 | h10
          · -- n > 23579830649
            rcases Nat.lt_or_ge 23632403989 n with h12 | h12
            · -- n > 23632403989
              exact RamareSaouter2003.prime_interval_nat_ladder_c00362 n (by omega) (by omega)
            · -- n <= 23632403989
              exact RamareSaouter2003.prime_interval_nat_ladder_c00361 n (by omega) (by omega)
          · -- n <= 23579830649
            exact RamareSaouter2003.prime_interval_nat_ladder_c00360 n (by omega) (by omega)
        · -- n <= 23527379479
          rcases Nat.lt_or_ge 23422842407 n with h10 | h10
          · -- n > 23422842407
            rcases Nat.lt_or_ge 23475050143 n with h12 | h12
            · -- n > 23475050143
              exact RamareSaouter2003.prime_interval_nat_ladder_c00359 n (by omega) (by omega)
            · -- n <= 23475050143
              exact RamareSaouter2003.prime_interval_nat_ladder_c00358 n (by omega) (by omega)
          · -- n <= 23422842407
            exact RamareSaouter2003.prime_interval_nat_ladder_c00357 n (by omega) (by omega)
      · -- n <= 23370755783
        rcases Nat.lt_or_ge 23215220521 n with h8 | h8
        · -- n > 23215220521
          rcases Nat.lt_or_ge 23266945151 n with h10 | h10
          · -- n > 23266945151
            rcases Nat.lt_or_ge 23318790109 n with h12 | h12
            · -- n > 23318790109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00356 n (by omega) (by omega)
            · -- n <= 23318790109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00355 n (by omega) (by omega)
          · -- n <= 23266945151
            exact RamareSaouter2003.prime_interval_nat_ladder_c00354 n (by omega) (by omega)
        · -- n <= 23215220521
          rcases Nat.lt_or_ge 23112131249 n with h10 | h10
          · -- n > 23112131249
            rcases Nat.lt_or_ge 23163615973 n with h12 | h12
            · -- n > 23163615973
              exact RamareSaouter2003.prime_interval_nat_ladder_c00353 n (by omega) (by omega)
            · -- n <= 23163615973
              exact RamareSaouter2003.prime_interval_nat_ladder_c00352 n (by omega) (by omega)
          · -- n <= 23112131249
            exact RamareSaouter2003.prime_interval_nat_ladder_c00351 n (by omega) (by omega)
