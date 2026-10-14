-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T19:09:37.105757+00:00
-- url     : https://prove2.me/submissions/6445a92b-ec08-417c-bd57-89a82ae269c5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02394
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02395
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02396
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02397
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02398
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02399
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02400

theorem solution (n : Nat)
    (hn : 3042386133557 < n) (hupper : n <= 3443870585447) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3237508437749 n with h2 | h2
  · -- n > 3237508437749
    rcases Nat.lt_or_ge 3334971660353 n with h4 | h4
    · -- n > 3334971660353
      rcases Nat.lt_or_ge 3384798089063 n with h6 | h6
      · -- n > 3384798089063
        rcases Nat.lt_or_ge 3409989775681 n with h8 | h8
        · -- n > 3409989775681
          rcases Nat.lt_or_ge 3426888309353 n with h10 | h10
          · -- n > 3426888309353
            rcases Nat.lt_or_ge 3435368953759 n with h12 | h12
            · -- n > 3435368953759
              exact RamareSaouter2003.prime_interval_nat_ladder_c02400 n (by omega) (by omega)
            · -- n <= 3435368953759
              exact RamareSaouter2003.prime_interval_nat_ladder_c02399 n (by omega) (by omega)
          · -- n <= 3426888309353
            rcases Nat.lt_or_ge 3418428600547 n with h12 | h12
            · -- n > 3418428600547
              exact RamareSaouter2003.prime_interval_nat_ladder_c02398 n (by omega) (by omega)
            · -- n <= 3418428600547
              exact RamareSaouter2003.prime_interval_nat_ladder_c02397 n (by omega) (by omega)
        · -- n <= 3409989775681
          rcases Nat.lt_or_ge 3393174571253 n with h10 | h10
          · -- n > 3393174571253
            rcases Nat.lt_or_ge 3401571783037 n with h12 | h12
            · -- n > 3401571783037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02396 n (by omega) (by omega)
            · -- n <= 3401571783037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02395 n (by omega) (by omega)
          · -- n <= 3393174571253
            exact RamareSaouter2003.prime_interval_nat_ladder_c02394 n (by omega) (by omega)
      · -- n <= 3384798089063
        rcases Nat.lt_or_ge 3359792508997 n with h8 | h8
        · -- n > 3359792508997
          rcases Nat.lt_or_ge 3368107108939 n with h10 | h10
          · -- n > 3368107108939
            rcases Nat.lt_or_ge 3376442285323 n with h12 | h12
            · -- n > 3376442285323
              exact RamareSaouter2003.prime_interval_nat_ladder_c02393 n (by omega) (by omega)
            · -- n <= 3376442285323
              exact RamareSaouter2003.prime_interval_nat_ladder_c02392 n (by omega) (by omega)
          · -- n <= 3368107108939
            exact RamareSaouter2003.prime_interval_nat_ladder_c02391 n (by omega) (by omega)
        · -- n <= 3359792508997
          rcases Nat.lt_or_ge 3343224835253 n with h10 | h10
          · -- n > 3343224835253
            rcases Nat.lt_or_ge 3351498434633 n with h12 | h12
            · -- n > 3351498434633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02390 n (by omega) (by omega)
            · -- n <= 3351498434633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02389 n (by omega) (by omega)
          · -- n <= 3343224835253
            exact RamareSaouter2003.prime_interval_nat_ladder_c02388 n (by omega) (by omega)
    · -- n <= 3334971660353
      rcases Nat.lt_or_ge 3285878708921 n with h6 | h6
      · -- n > 3285878708921
        rcases Nat.lt_or_ge 3310334178587 n with h8 | h8
        · -- n > 3310334178587
          rcases Nat.lt_or_ge 3318526382239 n with h10 | h10
          · -- n > 3318526382239
            rcases Nat.lt_or_ge 3326738859427 n with h12 | h12
            · -- n > 3326738859427
              exact RamareSaouter2003.prime_interval_nat_ladder_c02387 n (by omega) (by omega)
            · -- n <= 3326738859427
              exact RamareSaouter2003.prime_interval_nat_ladder_c02386 n (by omega) (by omega)
          · -- n <= 3318526382239
            exact RamareSaouter2003.prime_interval_nat_ladder_c02385 n (by omega) (by omega)
        · -- n <= 3310334178587
          rcases Nat.lt_or_ge 3294010391759 n with h10 | h10
          · -- n > 3294010391759
            rcases Nat.lt_or_ge 3302162198389 n with h12 | h12
            · -- n > 3302162198389
              exact RamareSaouter2003.prime_interval_nat_ladder_c02384 n (by omega) (by omega)
            · -- n <= 3302162198389
              exact RamareSaouter2003.prime_interval_nat_ladder_c02383 n (by omega) (by omega)
          · -- n <= 3294010391759
            exact RamareSaouter2003.prime_interval_nat_ladder_c02382 n (by omega) (by omega)
      · -- n <= 3285878708921
        rcases Nat.lt_or_ge 3261603906917 n with h8 | h8
        · -- n > 3261603906917
          rcases Nat.lt_or_ge 3269675515993 n with h10 | h10
          · -- n > 3269675515993
            rcases Nat.lt_or_ge 3277767100193 n with h12 | h12
            · -- n > 3277767100193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02381 n (by omega) (by omega)
            · -- n <= 3277767100193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02380 n (by omega) (by omega)
          · -- n <= 3269675515993
            exact RamareSaouter2003.prime_interval_nat_ladder_c02379 n (by omega) (by omega)
        · -- n <= 3261603906917
          rcases Nat.lt_or_ge 3245520416923 n with h10 | h10
          · -- n > 3245520416923
            rcases Nat.lt_or_ge 3253552223587 n with h12 | h12
            · -- n > 3253552223587
              exact RamareSaouter2003.prime_interval_nat_ladder_c02378 n (by omega) (by omega)
            · -- n <= 3253552223587
              exact RamareSaouter2003.prime_interval_nat_ladder_c02377 n (by omega) (by omega)
          · -- n <= 3245520416923
            exact RamareSaouter2003.prime_interval_nat_ladder_c02376 n (by omega) (by omega)
  · -- n <= 3237508437749
    rcases Nat.lt_or_ge 3135063090373 n with h4 | h4
    · -- n > 3135063090373
      rcases Nat.lt_or_ge 3181975658333 n with h6 | h6
      · -- n > 3181975658333
        rcases Nat.lt_or_ge 3205657819451 n with h8 | h8
        · -- n > 3205657819451
          rcases Nat.lt_or_ge 3221543766373 n with h10 | h10
          · -- n > 3221543766373
            rcases Nat.lt_or_ge 3229516237187 n with h12 | h12
            · -- n > 3229516237187
              exact RamareSaouter2003.prime_interval_nat_ladder_c02375 n (by omega) (by omega)
            · -- n <= 3229516237187
              exact RamareSaouter2003.prime_interval_nat_ladder_c02374 n (by omega) (by omega)
          · -- n <= 3221543766373
            rcases Nat.lt_or_ge 3213590976773 n with h12 | h12
            · -- n > 3213590976773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02373 n (by omega) (by omega)
            · -- n <= 3213590976773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02372 n (by omega) (by omega)
        · -- n <= 3205657819451
          rcases Nat.lt_or_ge 3189850208507 n with h10 | h10
          · -- n > 3189850208507
            rcases Nat.lt_or_ge 3197744246131 n with h12 | h12
            · -- n > 3197744246131
              exact RamareSaouter2003.prime_interval_nat_ladder_c02371 n (by omega) (by omega)
            · -- n <= 3197744246131
              exact RamareSaouter2003.prime_interval_nat_ladder_c02370 n (by omega) (by omega)
          · -- n <= 3189850208507
            exact RamareSaouter2003.prime_interval_nat_ladder_c02369 n (by omega) (by omega)
      · -- n <= 3181975658333
        rcases Nat.lt_or_ge 3158464018847 n with h8 | h8
        · -- n > 3158464018847
          rcases Nat.lt_or_ge 3166284827939 n with h10 | h10
          · -- n > 3166284827939
            rcases Nat.lt_or_ge 3174120547469 n with h12 | h12
            · -- n > 3174120547469
              exact RamareSaouter2003.prime_interval_nat_ladder_c02368 n (by omega) (by omega)
            · -- n <= 3174120547469
              exact RamareSaouter2003.prime_interval_nat_ladder_c02367 n (by omega) (by omega)
          · -- n <= 3166284827939
            exact RamareSaouter2003.prime_interval_nat_ladder_c02366 n (by omega) (by omega)
        · -- n <= 3158464018847
          rcases Nat.lt_or_ge 3142853140957 n with h10 | h10
          · -- n > 3142853140957
            rcases Nat.lt_or_ge 3150653453413 n with h12 | h12
            · -- n > 3150653453413
              exact RamareSaouter2003.prime_interval_nat_ladder_c02365 n (by omega) (by omega)
            · -- n <= 3150653453413
              exact RamareSaouter2003.prime_interval_nat_ladder_c02364 n (by omega) (by omega)
          · -- n <= 3142853140957
            exact RamareSaouter2003.prime_interval_nat_ladder_c02363 n (by omega) (by omega)
    · -- n <= 3135063090373
      rcases Nat.lt_or_ge 3088538786401 n with h6 | h6
      · -- n > 3088538786401
        rcases Nat.lt_or_ge 3111754599571 n with h8 | h8
        · -- n > 3111754599571
          rcases Nat.lt_or_ge 3119513810759 n with h10 | h10
          · -- n > 3119513810759
            rcases Nat.lt_or_ge 3127283310653 n with h12 | h12
            · -- n > 3127283310653
              exact RamareSaouter2003.prime_interval_nat_ladder_c02362 n (by omega) (by omega)
            · -- n <= 3127283310653
              exact RamareSaouter2003.prime_interval_nat_ladder_c02361 n (by omega) (by omega)
          · -- n <= 3119513810759
            exact RamareSaouter2003.prime_interval_nat_ladder_c02360 n (by omega) (by omega)
        · -- n <= 3111754599571
          rcases Nat.lt_or_ge 3096267078661 n with h10 | h10
          · -- n > 3096267078661
            rcases Nat.lt_or_ge 3104005685951 n with h12 | h12
            · -- n > 3104005685951
              exact RamareSaouter2003.prime_interval_nat_ladder_c02359 n (by omega) (by omega)
            · -- n <= 3104005685951
              exact RamareSaouter2003.prime_interval_nat_ladder_c02358 n (by omega) (by omega)
          · -- n <= 3096267078661
            exact RamareSaouter2003.prime_interval_nat_ladder_c02357 n (by omega) (by omega)
      · -- n <= 3088538786401
        rcases Nat.lt_or_ge 3065415886943 n with h8 | h8
        · -- n > 3065415886943
          rcases Nat.lt_or_ge 3073113181981 n with h10 | h10
          · -- n > 3073113181981
            rcases Nat.lt_or_ge 3080820817973 n with h12 | h12
            · -- n > 3080820817973
              exact RamareSaouter2003.prime_interval_nat_ladder_c02356 n (by omega) (by omega)
            · -- n <= 3080820817973
              exact RamareSaouter2003.prime_interval_nat_ladder_c02355 n (by omega) (by omega)
          · -- n <= 3073113181981
            exact RamareSaouter2003.prime_interval_nat_ladder_c02354 n (by omega) (by omega)
        · -- n <= 3065415886943
          rcases Nat.lt_or_ge 3050052354211 n with h10 | h10
          · -- n > 3050052354211
            rcases Nat.lt_or_ge 3057728941523 n with h12 | h12
            · -- n > 3057728941523
              exact RamareSaouter2003.prime_interval_nat_ladder_c02353 n (by omega) (by omega)
            · -- n <= 3057728941523
              exact RamareSaouter2003.prime_interval_nat_ladder_c02352 n (by omega) (by omega)
          · -- n <= 3050052354211
            exact RamareSaouter2003.prime_interval_nat_ladder_c02351 n (by omega) (by omega)
