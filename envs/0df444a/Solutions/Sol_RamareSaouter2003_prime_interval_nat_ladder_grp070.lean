-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:10:46.231227+00:00
-- url     : https://prove2.me/submissions/28415175-07c8-4028-8f62-ff3286b44394

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03500

theorem solution (n : Nat)
    (hn : 46148248066457 < n) (hupper : n <= 52218819183697) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 49089785306293 n with h2 | h2
  · -- n > 49089785306293
    rcases Nat.lt_or_ge 50567603444299 n with h4 | h4
    · -- n > 50567603444299
      rcases Nat.lt_or_ge 51323113043669 n with h6 | h6
      · -- n > 51323113043669
        rcases Nat.lt_or_ge 51705090270149 n with h8 | h8
        · -- n > 51705090270149
          rcases Nat.lt_or_ge 51961319841757 n with h10 | h10
          · -- n > 51961319841757
            rcases Nat.lt_or_ge 52089910398881 n with h12 | h12
            · -- n > 52089910398881
              exact RamareSaouter2003.prime_interval_nat_ladder_c03500 n (by omega) (by omega)
            · -- n <= 52089910398881
              exact RamareSaouter2003.prime_interval_nat_ladder_c03499 n (by omega) (by omega)
          · -- n <= 51961319841757
            rcases Nat.lt_or_ge 51833046726667 n with h12 | h12
            · -- n > 51833046726667
              exact RamareSaouter2003.prime_interval_nat_ladder_c03498 n (by omega) (by omega)
            · -- n <= 51833046726667
              exact RamareSaouter2003.prime_interval_nat_ladder_c03497 n (by omega) (by omega)
        · -- n <= 51705090270149
          rcases Nat.lt_or_ge 51450124207439 n with h10 | h10
          · -- n > 51450124207439
            rcases Nat.lt_or_ge 51577449690317 n with h12 | h12
            · -- n > 51577449690317
              exact RamareSaouter2003.prime_interval_nat_ladder_c03496 n (by omega) (by omega)
            · -- n <= 51577449690317
              exact RamareSaouter2003.prime_interval_nat_ladder_c03495 n (by omega) (by omega)
          · -- n <= 51450124207439
            exact RamareSaouter2003.prime_interval_nat_ladder_c03494 n (by omega) (by omega)
      · -- n <= 51323113043669
        rcases Nat.lt_or_ge 50943957717463 n with h8 | h8
        · -- n > 50943957717463
          rcases Nat.lt_or_ge 51070030571821 n with h10 | h10
          · -- n > 51070030571821
            rcases Nat.lt_or_ge 51196415423143 n with h12 | h12
            · -- n > 51196415423143
              exact RamareSaouter2003.prime_interval_nat_ladder_c03493 n (by omega) (by omega)
            · -- n <= 51196415423143
              exact RamareSaouter2003.prime_interval_nat_ladder_c03492 n (by omega) (by omega)
          · -- n <= 51070030571821
            exact RamareSaouter2003.prime_interval_nat_ladder_c03491 n (by omega) (by omega)
        · -- n <= 50943957717463
          rcases Nat.lt_or_ge 50692744921123 n with h10 | h10
          · -- n > 50692744921123
            rcases Nat.lt_or_ge 50818196090047 n with h12 | h12
            · -- n > 50818196090047
              exact RamareSaouter2003.prime_interval_nat_ladder_c03490 n (by omega) (by omega)
            · -- n <= 50818196090047
              exact RamareSaouter2003.prime_interval_nat_ladder_c03489 n (by omega) (by omega)
          · -- n <= 50692744921123
            exact RamareSaouter2003.prime_interval_nat_ladder_c03488 n (by omega) (by omega)
    · -- n <= 50567603444299
      rcases Nat.lt_or_ge 49823215437557 n with h6 | h6
      · -- n > 49823215437557
        rcases Nat.lt_or_ge 50194029531091 n with h8 | h8
        · -- n > 50194029531091
          rcases Nat.lt_or_ge 50318246511017 n with h10 | h10
          · -- n > 50318246511017
            rcases Nat.lt_or_ge 50442770895151 n with h12 | h12
            · -- n > 50442770895151
              exact RamareSaouter2003.prime_interval_nat_ladder_c03487 n (by omega) (by omega)
            · -- n <= 50442770895151
              exact RamareSaouter2003.prime_interval_nat_ladder_c03486 n (by omega) (by omega)
          · -- n <= 50318246511017
            exact RamareSaouter2003.prime_interval_nat_ladder_c03485 n (by omega) (by omega)
        · -- n <= 50194029531091
          rcases Nat.lt_or_ge 49946514750437 n with h10 | h10
          · -- n > 49946514750437
            rcases Nat.lt_or_ge 50070119196523 n with h12 | h12
            · -- n > 50070119196523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03484 n (by omega) (by omega)
            · -- n <= 50070119196523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03483 n (by omega) (by omega)
          · -- n <= 49946514750437
            exact RamareSaouter2003.prime_interval_nat_ladder_c03482 n (by omega) (by omega)
      · -- n <= 49823215437557
        rcases Nat.lt_or_ge 49455140775289 n with h8 | h8
        · -- n > 49455140775289
          rcases Nat.lt_or_ge 49577529200501 n with h10 | h10
          · -- n > 49577529200501
            rcases Nat.lt_or_ge 49700220504643 n with h12 | h12
            · -- n > 49700220504643
              exact RamareSaouter2003.prime_interval_nat_ladder_c03481 n (by omega) (by omega)
            · -- n <= 49700220504643
              exact RamareSaouter2003.prime_interval_nat_ladder_c03480 n (by omega) (by omega)
          · -- n <= 49577529200501
            exact RamareSaouter2003.prime_interval_nat_ladder_c03479 n (by omega) (by omega)
        · -- n <= 49455140775289
          rcases Nat.lt_or_ge 49211269573121 n with h10 | h10
          · -- n > 49211269573121
            rcases Nat.lt_or_ge 49333054481449 n with h12 | h12
            · -- n > 49333054481449
              exact RamareSaouter2003.prime_interval_nat_ladder_c03478 n (by omega) (by omega)
            · -- n <= 49333054481449
              exact RamareSaouter2003.prime_interval_nat_ladder_c03477 n (by omega) (by omega)
          · -- n <= 49211269573121
            exact RamareSaouter2003.prime_interval_nat_ladder_c03476 n (by omega) (by omega)
  · -- n <= 49089785306293
    rcases Nat.lt_or_ge 47537513014403 n with h4 | h4
    · -- n > 47537513014403
      rcases Nat.lt_or_ge 48247751288873 n with h6 | h6
      · -- n > 48247751288873
        rcases Nat.lt_or_ge 48606839838043 n with h8 | h8
        · -- n > 48606839838043
          rcases Nat.lt_or_ge 48847715730313 n with h10 | h10
          · -- n > 48847715730313
            rcases Nat.lt_or_ge 48968600938801 n with h12 | h12
            · -- n > 48968600938801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03475 n (by omega) (by omega)
            · -- n <= 48968600938801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03474 n (by omega) (by omega)
          · -- n <= 48847715730313
            rcases Nat.lt_or_ge 48727128942287 n with h12 | h12
            · -- n > 48727128942287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03473 n (by omega) (by omega)
            · -- n <= 48727128942287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03472 n (by omega) (by omega)
        · -- n <= 48606839838043
          rcases Nat.lt_or_ge 48367151743439 n with h10 | h10
          · -- n > 48367151743439
            rcases Nat.lt_or_ge 48486847682771 n with h12 | h12
            · -- n > 48486847682771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03471 n (by omega) (by omega)
            · -- n <= 48486847682771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03470 n (by omega) (by omega)
          · -- n <= 48367151743439
            exact RamareSaouter2003.prime_interval_nat_ladder_c03469 n (by omega) (by omega)
      · -- n <= 48247751288873
        rcases Nat.lt_or_ge 47891315546869 n with h8 | h8
        · -- n > 47891315546869
          rcases Nat.lt_or_ge 48009833917193 n with h10 | h10
          · -- n > 48009833917193
            rcases Nat.lt_or_ge 48128645589257 n with h12 | h12
            · -- n > 48128645589257
              exact RamareSaouter2003.prime_interval_nat_ladder_c03468 n (by omega) (by omega)
            · -- n <= 48128645589257
              exact RamareSaouter2003.prime_interval_nat_ladder_c03467 n (by omega) (by omega)
          · -- n <= 48009833917193
            exact RamareSaouter2003.prime_interval_nat_ladder_c03466 n (by omega) (by omega)
        · -- n <= 47891315546869
          rcases Nat.lt_or_ge 47655155816743 n with h10 | h10
          · -- n > 47655155816743
            rcases Nat.lt_or_ge 47773089754123 n with h12 | h12
            · -- n > 47773089754123
              exact RamareSaouter2003.prime_interval_nat_ladder_c03465 n (by omega) (by omega)
            · -- n <= 47773089754123
              exact RamareSaouter2003.prime_interval_nat_ladder_c03464 n (by omega) (by omega)
          · -- n <= 47655155816743
            exact RamareSaouter2003.prime_interval_nat_ladder_c03463 n (by omega) (by omega)
    · -- n <= 47537513014403
      rcases Nat.lt_or_ge 46837729909261 n with h6 | h6
      · -- n > 46837729909261
        rcases Nat.lt_or_ge 47186324238331 n with h8 | h8
        · -- n > 47186324238331
          rcases Nat.lt_or_ge 47303097941201 n with h10 | h10
          · -- n > 47303097941201
            rcases Nat.lt_or_ge 47420160628171 n with h12 | h12
            · -- n > 47420160628171
              exact RamareSaouter2003.prime_interval_nat_ladder_c03462 n (by omega) (by omega)
            · -- n <= 47420160628171
              exact RamareSaouter2003.prime_interval_nat_ladder_c03461 n (by omega) (by omega)
          · -- n <= 47303097941201
            exact RamareSaouter2003.prime_interval_nat_ladder_c03460 n (by omega) (by omega)
        · -- n <= 47186324238331
          rcases Nat.lt_or_ge 46953640933079 n with h10 | h10
          · -- n > 46953640933079
            rcases Nat.lt_or_ge 47069838806131 n with h12 | h12
            · -- n > 47069838806131
              exact RamareSaouter2003.prime_interval_nat_ladder_c03459 n (by omega) (by omega)
            · -- n <= 47069838806131
              exact RamareSaouter2003.prime_interval_nat_ladder_c03458 n (by omega) (by omega)
          · -- n <= 46953640933079
            exact RamareSaouter2003.prime_interval_nat_ladder_c03457 n (by omega) (by omega)
      · -- n <= 46837729909261
        rcases Nat.lt_or_ge 46491710860487 n with h8 | h8
        · -- n > 46491710860487
          rcases Nat.lt_or_ge 46606765578403 n with h10 | h10
          · -- n > 46606765578403
            rcases Nat.lt_or_ge 46722105026503 n with h12 | h12
            · -- n > 46722105026503
              exact RamareSaouter2003.prime_interval_nat_ladder_c03456 n (by omega) (by omega)
            · -- n <= 46722105026503
              exact RamareSaouter2003.prime_interval_nat_ladder_c03455 n (by omega) (by omega)
          · -- n <= 46606765578403
            exact RamareSaouter2003.prime_interval_nat_ladder_c03454 n (by omega) (by omega)
        · -- n <= 46491710860487
          rcases Nat.lt_or_ge 46262452804739 n with h10 | h10
          · -- n > 46262452804739
            rcases Nat.lt_or_ge 46376940169613 n with h12 | h12
            · -- n > 46376940169613
              exact RamareSaouter2003.prime_interval_nat_ladder_c03453 n (by omega) (by omega)
            · -- n <= 46376940169613
              exact RamareSaouter2003.prime_interval_nat_ladder_c03452 n (by omega) (by omega)
          · -- n <= 46262452804739
            exact RamareSaouter2003.prime_interval_nat_ladder_c03451 n (by omega) (by omega)
