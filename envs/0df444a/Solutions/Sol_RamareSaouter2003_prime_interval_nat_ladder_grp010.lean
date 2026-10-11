-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T19:25:42.649933+00:00
-- url     : https://prove2.me/submissions/200675cd-5de4-4035-bff5-6af78cb295c5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00500

theorem solution (n : Nat)
    (hn : 28838600017 < n) (hupper : n <= 32276278889) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 30506998217 n with h2 | h2
  · -- n > 30506998217
    rcases Nat.lt_or_ge 31343324423 n with h4 | h4
    · -- n > 31343324423
      rcases Nat.lt_or_ge 31770424379 n with h6 | h6
      · -- n > 31770424379
        rcases Nat.lt_or_ge 31986218731 n with h8 | h8
        · -- n > 31986218731
          rcases Nat.lt_or_ge 32130914029 n with h10 | h10
          · -- n > 32130914029
            rcases Nat.lt_or_ge 32203512577 n with h12 | h12
            · -- n > 32203512577
              exact RamareSaouter2003.prime_interval_nat_ladder_c00500 n (by omega) (by omega)
            · -- n <= 32203512577
              exact RamareSaouter2003.prime_interval_nat_ladder_c00499 n (by omega) (by omega)
          · -- n <= 32130914029
            rcases Nat.lt_or_ge 32058482893 n with h12 | h12
            · -- n > 32058482893
              exact RamareSaouter2003.prime_interval_nat_ladder_c00498 n (by omega) (by omega)
            · -- n <= 32058482893
              exact RamareSaouter2003.prime_interval_nat_ladder_c00497 n (by omega) (by omega)
        · -- n <= 31986218731
          rcases Nat.lt_or_ge 31842189877 n with h10 | h10
          · -- n > 31842189877
            rcases Nat.lt_or_ge 31914121181 n with h12 | h12
            · -- n > 31914121181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00496 n (by omega) (by omega)
            · -- n <= 31914121181
              exact RamareSaouter2003.prime_interval_nat_ladder_c00495 n (by omega) (by omega)
          · -- n <= 31842189877
            exact RamareSaouter2003.prime_interval_nat_ladder_c00494 n (by omega) (by omega)
      · -- n <= 31770424379
        rcases Nat.lt_or_ge 31556122069 n with h8 | h8
        · -- n > 31556122069
          rcases Nat.lt_or_ge 31627389307 n with h10 | h10
          · -- n > 31627389307
            rcases Nat.lt_or_ge 31698824347 n with h12 | h12
            · -- n > 31698824347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00493 n (by omega) (by omega)
            · -- n <= 31698824347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00492 n (by omega) (by omega)
          · -- n <= 31627389307
            exact RamareSaouter2003.prime_interval_nat_ladder_c00491 n (by omega) (by omega)
        · -- n <= 31556122069
          rcases Nat.lt_or_ge 31414090027 n with h10 | h10
          · -- n > 31414090027
            rcases Nat.lt_or_ge 31485022477 n with h12 | h12
            · -- n > 31485022477
              exact RamareSaouter2003.prime_interval_nat_ladder_c00490 n (by omega) (by omega)
            · -- n <= 31485022477
              exact RamareSaouter2003.prime_interval_nat_ladder_c00489 n (by omega) (by omega)
          · -- n <= 31414090027
            exact RamareSaouter2003.prime_interval_nat_ladder_c00488 n (by omega) (by omega)
    · -- n <= 31343324423
      rcases Nat.lt_or_ge 30922210169 n with h6 | h6
      · -- n > 30922210169
        rcases Nat.lt_or_ge 31132024081 n with h8 | h8
        · -- n > 31132024081
          rcases Nat.lt_or_ge 31202291837 n with h10 | h10
          · -- n > 31202291837
            rcases Nat.lt_or_ge 31272725149 n with h12 | h12
            · -- n > 31272725149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00487 n (by omega) (by omega)
            · -- n <= 31272725149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00486 n (by omega) (by omega)
          · -- n <= 31202291837
            exact RamareSaouter2003.prime_interval_nat_ladder_c00485 n (by omega) (by omega)
        · -- n <= 31132024081
          rcases Nat.lt_or_ge 30991983667 n with h10 | h10
          · -- n > 30991983667
            rcases Nat.lt_or_ge 31061921497 n with h12 | h12
            · -- n > 31061921497
              exact RamareSaouter2003.prime_interval_nat_ladder_c00484 n (by omega) (by omega)
            · -- n <= 31061921497
              exact RamareSaouter2003.prime_interval_nat_ladder_c00483 n (by omega) (by omega)
          · -- n <= 30991983667
            exact RamareSaouter2003.prime_interval_nat_ladder_c00482 n (by omega) (by omega)
      · -- n <= 30922210169
        rcases Nat.lt_or_ge 30713871821 n with h8 | h8
        · -- n > 30713871821
          rcases Nat.lt_or_ge 30783154673 n with h10 | h10
          · -- n > 30783154673
            rcases Nat.lt_or_ge 30852600677 n with h12 | h12
            · -- n > 30852600677
              exact RamareSaouter2003.prime_interval_nat_ladder_c00481 n (by omega) (by omega)
            · -- n <= 30852600677
              exact RamareSaouter2003.prime_interval_nat_ladder_c00480 n (by omega) (by omega)
          · -- n <= 30783154673
            exact RamareSaouter2003.prime_interval_nat_ladder_c00479 n (by omega) (by omega)
        · -- n <= 30713871821
          rcases Nat.lt_or_ge 30575794003 n with h10 | h10
          · -- n > 30575794003
            rcases Nat.lt_or_ge 30644751751 n with h12 | h12
            · -- n > 30644751751
              exact RamareSaouter2003.prime_interval_nat_ladder_c00478 n (by omega) (by omega)
            · -- n <= 30644751751
              exact RamareSaouter2003.prime_interval_nat_ladder_c00477 n (by omega) (by omega)
          · -- n <= 30575794003
            exact RamareSaouter2003.prime_interval_nat_ladder_c00476 n (by omega) (by omega)
  · -- n <= 30506998217
    rcases Nat.lt_or_ge 29627212541 n with h4 | h4
    · -- n > 29627212541
      rcases Nat.lt_or_ge 30029929459 n with h6 | h6
      · -- n > 30029929459
        rcases Nat.lt_or_ge 30233426747 n with h8 | h8
        · -- n > 30233426747
          rcases Nat.lt_or_ge 30369890939 n with h10 | h10
          · -- n > 30369890939
            rcases Nat.lt_or_ge 30438364001 n with h12 | h12
            · -- n > 30438364001
              exact RamareSaouter2003.prime_interval_nat_ladder_c00475 n (by omega) (by omega)
            · -- n <= 30438364001
              exact RamareSaouter2003.prime_interval_nat_ladder_c00474 n (by omega) (by omega)
          · -- n <= 30369890939
            rcases Nat.lt_or_ge 30301578653 n with h12 | h12
            · -- n > 30301578653
              exact RamareSaouter2003.prime_interval_nat_ladder_c00473 n (by omega) (by omega)
            · -- n <= 30301578653
              exact RamareSaouter2003.prime_interval_nat_ladder_c00472 n (by omega) (by omega)
        · -- n <= 30233426747
          rcases Nat.lt_or_ge 30097602571 n with h10 | h10
          · -- n > 30097602571
            rcases Nat.lt_or_ge 30165434837 n with h12 | h12
            · -- n > 30165434837
              exact RamareSaouter2003.prime_interval_nat_ladder_c00471 n (by omega) (by omega)
            · -- n <= 30165434837
              exact RamareSaouter2003.prime_interval_nat_ladder_c00470 n (by omega) (by omega)
          · -- n <= 30097602571
            exact RamareSaouter2003.prime_interval_nat_ladder_c00469 n (by omega) (by omega)
      · -- n <= 30029929459
        rcases Nat.lt_or_ge 29827861507 n with h8 | h8
        · -- n > 29827861507
          rcases Nat.lt_or_ge 29895059323 n with h10 | h10
          · -- n > 29895059323
            rcases Nat.lt_or_ge 29962415159 n with h12 | h12
            · -- n > 29962415159
              exact RamareSaouter2003.prime_interval_nat_ladder_c00468 n (by omega) (by omega)
            · -- n <= 29962415159
              exact RamareSaouter2003.prime_interval_nat_ladder_c00467 n (by omega) (by omega)
          · -- n <= 29895059323
            exact RamareSaouter2003.prime_interval_nat_ladder_c00466 n (by omega) (by omega)
        · -- n <= 29827861507
          rcases Nat.lt_or_ge 29693938537 n with h10 | h10
          · -- n > 29693938537
            rcases Nat.lt_or_ge 29760821393 n with h12 | h12
            · -- n > 29760821393
              exact RamareSaouter2003.prime_interval_nat_ladder_c00465 n (by omega) (by omega)
            · -- n <= 29760821393
              exact RamareSaouter2003.prime_interval_nat_ladder_c00464 n (by omega) (by omega)
          · -- n <= 29693938537
            exact RamareSaouter2003.prime_interval_nat_ladder_c00463 n (by omega) (by omega)
    · -- n <= 29627212541
      rcases Nat.lt_or_ge 29230130057 n with h6 | h6
      · -- n > 29230130057
        rcases Nat.lt_or_ge 29427972199 n with h8 | h8
        · -- n > 29427972199
          rcases Nat.lt_or_ge 29494229771 n with h10 | h10
          · -- n > 29494229771
            rcases Nat.lt_or_ge 29560643111 n with h12 | h12
            · -- n > 29560643111
              exact RamareSaouter2003.prime_interval_nat_ladder_c00462 n (by omega) (by omega)
            · -- n <= 29560643111
              exact RamareSaouter2003.prime_interval_nat_ladder_c00461 n (by omega) (by omega)
          · -- n <= 29494229771
            exact RamareSaouter2003.prime_interval_nat_ladder_c00460 n (by omega) (by omega)
        · -- n <= 29427972199
          rcases Nat.lt_or_ge 29295922709 n with h10 | h10
          · -- n > 29295922709
            rcases Nat.lt_or_ge 29361869951 n with h12 | h12
            · -- n > 29361869951
              exact RamareSaouter2003.prime_interval_nat_ladder_c00459 n (by omega) (by omega)
            · -- n <= 29361869951
              exact RamareSaouter2003.prime_interval_nat_ladder_c00458 n (by omega) (by omega)
          · -- n <= 29295922709
            exact RamareSaouter2003.prime_interval_nat_ladder_c00457 n (by omega) (by omega)
      · -- n <= 29230130057
        rcases Nat.lt_or_ge 29033676037 n with h8 | h8
        · -- n > 29033676037
          rcases Nat.lt_or_ge 29099007107 n with h10 | h10
          · -- n > 29099007107
            rcases Nat.lt_or_ge 29164491677 n with h12 | h12
            · -- n > 29164491677
              exact RamareSaouter2003.prime_interval_nat_ladder_c00456 n (by omega) (by omega)
            · -- n <= 29164491677
              exact RamareSaouter2003.prime_interval_nat_ladder_c00455 n (by omega) (by omega)
          · -- n <= 29099007107
            exact RamareSaouter2003.prime_interval_nat_ladder_c00454 n (by omega) (by omega)
        · -- n <= 29033676037
          rcases Nat.lt_or_ge 28903472909 n with h10 | h10
          · -- n > 28903472909
            rcases Nat.lt_or_ge 28968498109 n with h12 | h12
            · -- n > 28968498109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00453 n (by omega) (by omega)
            · -- n <= 28968498109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00452 n (by omega) (by omega)
          · -- n <= 28903472909
            exact RamareSaouter2003.prime_interval_nat_ladder_c00451 n (by omega) (by omega)
