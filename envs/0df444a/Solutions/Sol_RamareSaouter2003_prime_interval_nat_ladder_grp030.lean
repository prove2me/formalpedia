-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T08:07:18.930333+00:00
-- url     : https://prove2.me/submissions/c77d1436-2fbd-4c21-a10d-5e42b2cae2e0

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01500

theorem solution (n : Nat)
    (hn : 312172099721 < n) (hupper : n <= 354000949151) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 332423192623 n with h2 | h2
  · -- n > 332423192623
    rcases Nat.lt_or_ge 342609677981 n with h4 | h4
    · -- n > 342609677981
      rcases Nat.lt_or_ge 347820483317 n with h6 | h6
      · -- n > 347820483317
        rcases Nat.lt_or_ge 350455807579 n with h8 | h8
        · -- n > 350455807579
          rcases Nat.lt_or_ge 352223876929 n with h10 | h10
          · -- n > 352223876929
            rcases Nat.lt_or_ge 353111284819 n with h12 | h12
            · -- n > 353111284819
              exact RamareSaouter2003.prime_interval_nat_ladder_c01500 n (by omega) (by omega)
            · -- n <= 353111284819
              exact RamareSaouter2003.prime_interval_nat_ladder_c01499 n (by omega) (by omega)
          · -- n <= 352223876929
            rcases Nat.lt_or_ge 351338719813 n with h12 | h12
            · -- n > 351338719813
              exact RamareSaouter2003.prime_interval_nat_ladder_c01498 n (by omega) (by omega)
            · -- n <= 351338719813
              exact RamareSaouter2003.prime_interval_nat_ladder_c01497 n (by omega) (by omega)
        · -- n <= 350455807579
          rcases Nat.lt_or_ge 348696695059 n with h10 | h10
          · -- n > 348696695059
            rcases Nat.lt_or_ge 349575134569 n with h12 | h12
            · -- n > 349575134569
              exact RamareSaouter2003.prime_interval_nat_ladder_c01496 n (by omega) (by omega)
            · -- n <= 349575134569
              exact RamareSaouter2003.prime_interval_nat_ladder_c01495 n (by omega) (by omega)
          · -- n <= 348696695059
            exact RamareSaouter2003.prime_interval_nat_ladder_c01494 n (by omega) (by omega)
      · -- n <= 347820483317
        rcases Nat.lt_or_ge 345205157911 n with h8 | h8
        · -- n > 345205157911
          rcases Nat.lt_or_ge 346074720469 n with h10 | h10
          · -- n > 346074720469
            rcases Nat.lt_or_ge 346946493659 n with h12 | h12
            · -- n > 346946493659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01493 n (by omega) (by omega)
            · -- n <= 346946493659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01492 n (by omega) (by omega)
          · -- n <= 346074720469
            exact RamareSaouter2003.prime_interval_nat_ladder_c01491 n (by omega) (by omega)
        · -- n <= 345205157911
          rcases Nat.lt_or_ge 343472642333 n with h10 | h10
          · -- n > 343472642333
            rcases Nat.lt_or_ge 344337800383 n with h12 | h12
            · -- n > 344337800383
              exact RamareSaouter2003.prime_interval_nat_ladder_c01490 n (by omega) (by omega)
            · -- n <= 344337800383
              exact RamareSaouter2003.prime_interval_nat_ladder_c01489 n (by omega) (by omega)
          · -- n <= 343472642333
            exact RamareSaouter2003.prime_interval_nat_ladder_c01488 n (by omega) (by omega)
    · -- n <= 342609677981
      rcases Nat.lt_or_ge 337477648159 n with h6 | h6
      · -- n > 337477648159
        rcases Nat.lt_or_ge 340033891709 n with h8 | h8
        · -- n > 340033891709
          rcases Nat.lt_or_ge 340890308261 n with h10 | h10
          · -- n > 340890308261
            rcases Nat.lt_or_ge 341748901873 n with h12 | h12
            · -- n > 341748901873
              exact RamareSaouter2003.prime_interval_nat_ladder_c01487 n (by omega) (by omega)
            · -- n <= 341748901873
              exact RamareSaouter2003.prime_interval_nat_ladder_c01486 n (by omega) (by omega)
          · -- n <= 340890308261
            exact RamareSaouter2003.prime_interval_nat_ladder_c01485 n (by omega) (by omega)
        · -- n <= 340033891709
          rcases Nat.lt_or_ge 338327567177 n with h10 | h10
          · -- n > 338327567177
            rcases Nat.lt_or_ge 339179646511 n with h12 | h12
            · -- n > 339179646511
              exact RamareSaouter2003.prime_interval_nat_ladder_c01484 n (by omega) (by omega)
            · -- n <= 339179646511
              exact RamareSaouter2003.prime_interval_nat_ladder_c01483 n (by omega) (by omega)
          · -- n <= 338327567177
            exact RamareSaouter2003.prime_interval_nat_ladder_c01482 n (by omega) (by omega)
      · -- n <= 337477648159
        rcases Nat.lt_or_ge 334940798051 n with h8 | h8
        · -- n > 334940798051
          rcases Nat.lt_or_ge 335784269201 n with h10 | h10
          · -- n > 335784269201
            rcases Nat.lt_or_ge 336629884039 n with h12 | h12
            · -- n > 336629884039
              exact RamareSaouter2003.prime_interval_nat_ladder_c01481 n (by omega) (by omega)
            · -- n <= 336629884039
              exact RamareSaouter2003.prime_interval_nat_ladder_c01480 n (by omega) (by omega)
          · -- n <= 335784269201
            exact RamareSaouter2003.prime_interval_nat_ladder_c01479 n (by omega) (by omega)
        · -- n <= 334940798051
          rcases Nat.lt_or_ge 333260265281 n with h10 | h10
          · -- n > 333260265281
            rcases Nat.lt_or_ge 334099465303 n with h12 | h12
            · -- n > 334099465303
              exact RamareSaouter2003.prime_interval_nat_ladder_c01478 n (by omega) (by omega)
            · -- n <= 334099465303
              exact RamareSaouter2003.prime_interval_nat_ladder_c01477 n (by omega) (by omega)
          · -- n <= 333260265281
            exact RamareSaouter2003.prime_interval_nat_ladder_c01476 n (by omega) (by omega)
  · -- n <= 332423192623
    rcases Nat.lt_or_ge 321732382507 n with h4 | h4
    · -- n > 321732382507
      rcases Nat.lt_or_ge 326622795391 n with h6 | h6
      · -- n > 326622795391
        rcases Nat.lt_or_ge 329096067319 n with h8 | h8
        · -- n > 329096067319
          rcases Nat.lt_or_ge 330755407819 n with h10 | h10
          · -- n > 330755407819
            rcases Nat.lt_or_ge 331588241923 n with h12 | h12
            · -- n > 331588241923
              exact RamareSaouter2003.prime_interval_nat_ladder_c01475 n (by omega) (by omega)
            · -- n <= 331588241923
              exact RamareSaouter2003.prime_interval_nat_ladder_c01474 n (by omega) (by omega)
          · -- n <= 330755407819
            rcases Nat.lt_or_ge 329924684699 n with h12 | h12
            · -- n > 329924684699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01473 n (by omega) (by omega)
            · -- n <= 329924684699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01472 n (by omega) (by omega)
        · -- n <= 329096067319
          rcases Nat.lt_or_ge 327445128007 n with h10 | h10
          · -- n > 327445128007
            rcases Nat.lt_or_ge 328269550207 n with h12 | h12
            · -- n > 328269550207
              exact RamareSaouter2003.prime_interval_nat_ladder_c01471 n (by omega) (by omega)
            · -- n <= 328269550207
              exact RamareSaouter2003.prime_interval_nat_ladder_c01470 n (by omega) (by omega)
          · -- n <= 327445128007
            exact RamareSaouter2003.prime_interval_nat_ladder_c01469 n (by omega) (by omega)
      · -- n <= 326622795391
        rcases Nat.lt_or_ge 324168281653 n with h8 | h8
        · -- n > 324168281653
          rcases Nat.lt_or_ge 324984377569 n with h10 | h10
          · -- n > 324984377569
            rcases Nat.lt_or_ge 325802547001 n with h12 | h12
            · -- n > 325802547001
              exact RamareSaouter2003.prime_interval_nat_ladder_c01468 n (by omega) (by omega)
            · -- n <= 325802547001
              exact RamareSaouter2003.prime_interval_nat_ladder_c01467 n (by omega) (by omega)
          · -- n <= 324984377569
            exact RamareSaouter2003.prime_interval_nat_ladder_c01466 n (by omega) (by omega)
        · -- n <= 324168281653
          rcases Nat.lt_or_ge 322542289429 n with h10 | h10
          · -- n > 322542289429
            rcases Nat.lt_or_ge 323354254049 n with h12 | h12
            · -- n > 323354254049
              exact RamareSaouter2003.prime_interval_nat_ladder_c01465 n (by omega) (by omega)
            · -- n <= 323354254049
              exact RamareSaouter2003.prime_interval_nat_ladder_c01464 n (by omega) (by omega)
          · -- n <= 322542289429
            exact RamareSaouter2003.prime_interval_nat_ladder_c01463 n (by omega) (by omega)
    · -- n <= 321732382507
      rcases Nat.lt_or_ge 316915859339 n with h6 | h6
      · -- n > 316915859339
        rcases Nat.lt_or_ge 319314955517 n with h8 | h8
        · -- n > 319314955517
          rcases Nat.lt_or_ge 320118720787 n with h10 | h10
          · -- n > 320118720787
            rcases Nat.lt_or_ge 320924528047 n with h12 | h12
            · -- n > 320924528047
              exact RamareSaouter2003.prime_interval_nat_ladder_c01462 n (by omega) (by omega)
            · -- n <= 320924528047
              exact RamareSaouter2003.prime_interval_nat_ladder_c01461 n (by omega) (by omega)
          · -- n <= 320118720787
            exact RamareSaouter2003.prime_interval_nat_ladder_c01460 n (by omega) (by omega)
        · -- n <= 319314955517
          rcases Nat.lt_or_ge 317713529983 n with h10 | h10
          · -- n > 317713529983
            rcases Nat.lt_or_ge 318513226991 n with h12 | h12
            · -- n > 318513226991
              exact RamareSaouter2003.prime_interval_nat_ladder_c01459 n (by omega) (by omega)
            · -- n <= 318513226991
              exact RamareSaouter2003.prime_interval_nat_ladder_c01458 n (by omega) (by omega)
          · -- n <= 317713529983
            exact RamareSaouter2003.prime_interval_nat_ladder_c01457 n (by omega) (by omega)
      · -- n <= 316915859339
        rcases Nat.lt_or_ge 314534953801 n with h8 | h8
        · -- n > 314534953801
          rcases Nat.lt_or_ge 315326576443 n with h10 | h10
          · -- n > 315326576443
            rcases Nat.lt_or_ge 316120209857 n with h12 | h12
            · -- n > 316120209857
              exact RamareSaouter2003.prime_interval_nat_ladder_c01456 n (by omega) (by omega)
            · -- n <= 316120209857
              exact RamareSaouter2003.prime_interval_nat_ladder_c01455 n (by omega) (by omega)
          · -- n <= 315326576443
            exact RamareSaouter2003.prime_interval_nat_ladder_c01454 n (by omega) (by omega)
        · -- n <= 314534953801
          rcases Nat.lt_or_ge 312957720589 n with h10 | h10
          · -- n > 312957720589
            rcases Nat.lt_or_ge 313745336899 n with h12 | h12
            · -- n > 313745336899
              exact RamareSaouter2003.prime_interval_nat_ladder_c01453 n (by omega) (by omega)
            · -- n <= 313745336899
              exact RamareSaouter2003.prime_interval_nat_ladder_c01452 n (by omega) (by omega)
          · -- n <= 312957720589
            exact RamareSaouter2003.prime_interval_nat_ladder_c01451 n (by omega) (by omega)
