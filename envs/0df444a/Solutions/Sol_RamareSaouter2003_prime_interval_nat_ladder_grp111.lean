-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T17:02:29.810294+00:00
-- url     : https://prove2.me/submissions/96c48aa4-472e-4978-b8e7-91716d5f5898

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05550

theorem solution (n : Nat)
    (hn : 12791132576439523 < n) (hupper : n <= 14733209110173557) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 13727866358159687 n with h2 | h2
  · -- n > 13727866358159687
    rcases Nat.lt_or_ge 14201574607919269 n with h4 | h4
    · -- n > 14201574607919269
      rcases Nat.lt_or_ge 14444510055564529 n with h6 | h6
      · -- n > 14444510055564529
        rcases Nat.lt_or_ge 14567538277156027 n with h8 | h8
        · -- n > 14567538277156027
          rcases Nat.lt_or_ge 14650136284158937 n with h10 | h10
          · -- n > 14650136284158937
            rcases Nat.lt_or_ge 14691613525422187 n with h12 | h12
            · -- n > 14691613525422187
              exact RamareSaouter2003.prime_interval_nat_ladder_c05550 n (by omega) (by omega)
            · -- n <= 14691613525422187
              exact RamareSaouter2003.prime_interval_nat_ladder_c05549 n (by omega) (by omega)
          · -- n <= 14650136284158937
            rcases Nat.lt_or_ge 14608779324167543 n with h12 | h12
            · -- n > 14608779324167543
              exact RamareSaouter2003.prime_interval_nat_ladder_c05548 n (by omega) (by omega)
            · -- n <= 14608779324167543
              exact RamareSaouter2003.prime_interval_nat_ladder_c05547 n (by omega) (by omega)
        · -- n <= 14567538277156027
          rcases Nat.lt_or_ge 14485400979323947 n with h10 | h10
          · -- n > 14485400979323947
            rcases Nat.lt_or_ge 14526410237019641 n with h12 | h12
            · -- n > 14526410237019641
              exact RamareSaouter2003.prime_interval_nat_ladder_c05546 n (by omega) (by omega)
            · -- n <= 14526410237019641
              exact RamareSaouter2003.prime_interval_nat_ladder_c05545 n (by omega) (by omega)
          · -- n <= 14485400979323947
            exact RamareSaouter2003.prime_interval_nat_ladder_c05544 n (by omega) (by omega)
      · -- n <= 14444510055564529
        rcases Nat.lt_or_ge 14322516481996687 n with h8 | h8
        · -- n > 14322516481996687
          rcases Nat.lt_or_ge 14363066236361959 n with h10 | h10
          · -- n > 14363066236361959
            rcases Nat.lt_or_ge 14403729722362459 n with h12 | h12
            · -- n > 14403729722362459
              exact RamareSaouter2003.prime_interval_nat_ladder_c05543 n (by omega) (by omega)
            · -- n <= 14403729722362459
              exact RamareSaouter2003.prime_interval_nat_ladder_c05542 n (by omega) (by omega)
          · -- n <= 14363066236361959
            exact RamareSaouter2003.prime_interval_nat_ladder_c05541 n (by omega) (by omega)
        · -- n <= 14322516481996687
          rcases Nat.lt_or_ge 14241768650105083 n with h10 | h10
          · -- n > 14241768650105083
            rcases Nat.lt_or_ge 14282085465734531 n with h12 | h12
            · -- n > 14282085465734531
              exact RamareSaouter2003.prime_interval_nat_ladder_c05540 n (by omega) (by omega)
            · -- n <= 14282085465734531
              exact RamareSaouter2003.prime_interval_nat_ladder_c05539 n (by omega) (by omega)
          · -- n <= 14241768650105083
            exact RamareSaouter2003.prime_interval_nat_ladder_c05538 n (by omega) (by omega)
    · -- n <= 14201574607919269
      rcases Nat.lt_or_ge 13962713110135121 n with h6 | h6
      · -- n > 13962713110135121
        rcases Nat.lt_or_ge 14081644157374193 n with h8 | h8
        · -- n > 14081644157374193
          rcases Nat.lt_or_ge 14121509488146427 n with h10 | h10
          · -- n > 14121509488146427
            rcases Nat.lt_or_ge 14161482814605013 n with h12 | h12
            · -- n > 14161482814605013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05537 n (by omega) (by omega)
            · -- n <= 14161482814605013
              exact RamareSaouter2003.prime_interval_nat_ladder_c05536 n (by omega) (by omega)
          · -- n <= 14121509488146427
            exact RamareSaouter2003.prime_interval_nat_ladder_c05535 n (by omega) (by omega)
        · -- n <= 14081644157374193
          rcases Nat.lt_or_ge 14002243716681421 n with h10 | h10
          · -- n > 14002243716681421
            rcases Nat.lt_or_ge 14041888268295577 n with h12 | h12
            · -- n > 14041888268295577
              exact RamareSaouter2003.prime_interval_nat_ladder_c05534 n (by omega) (by omega)
            · -- n <= 14041888268295577
              exact RamareSaouter2003.prime_interval_nat_ladder_c05533 n (by omega) (by omega)
          · -- n <= 14002243716681421
            exact RamareSaouter2003.prime_interval_nat_ladder_c05532 n (by omega) (by omega)
      · -- n <= 13962713110135121
        rcases Nat.lt_or_ge 13844785783946077 n with h8 | h8
        · -- n > 13844785783946077
          rcases Nat.lt_or_ge 13883984024041303 n with h10 | h10
          · -- n > 13883984024041303
            rcases Nat.lt_or_ge 13923293132301961 n with h12 | h12
            · -- n > 13923293132301961
              exact RamareSaouter2003.prime_interval_nat_ladder_c05531 n (by omega) (by omega)
            · -- n <= 13923293132301961
              exact RamareSaouter2003.prime_interval_nat_ladder_c05530 n (by omega) (by omega)
          · -- n <= 13883984024041303
            exact RamareSaouter2003.prime_interval_nat_ladder_c05529 n (by omega) (by omega)
        · -- n <= 13844785783946077
          rcases Nat.lt_or_ge 13766730127690759 n with h10 | h10
          · -- n > 13766730127690759
            rcases Nat.lt_or_ge 13805703352396693 n with h12 | h12
            · -- n > 13805703352396693
              exact RamareSaouter2003.prime_interval_nat_ladder_c05528 n (by omega) (by omega)
            · -- n <= 13805703352396693
              exact RamareSaouter2003.prime_interval_nat_ladder_c05527 n (by omega) (by omega)
          · -- n <= 13766730127690759
            exact RamareSaouter2003.prime_interval_nat_ladder_c05526 n (by omega) (by omega)
  · -- n <= 13727866358159687
    rcases Nat.lt_or_ge 13232493570143149 n with h4 | h4
    · -- n > 13232493570143149
      rcases Nat.lt_or_ge 13458865815480167 n with h6 | h6
      · -- n > 13458865815480167
        rcases Nat.lt_or_ge 13573506119811839 n with h8 | h8
        · -- n > 13573506119811839
          rcases Nat.lt_or_ge 13650474681278329 n with h10 | h10
          · -- n > 13650474681278329
            rcases Nat.lt_or_ge 13689123057791089 n with h12 | h12
            · -- n > 13689123057791089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05525 n (by omega) (by omega)
            · -- n <= 13689123057791089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05524 n (by omega) (by omega)
          · -- n <= 13650474681278329
            rcases Nat.lt_or_ge 13611936465570593 n with h12 | h12
            · -- n > 13611936465570593
              exact RamareSaouter2003.prime_interval_nat_ladder_c05523 n (by omega) (by omega)
            · -- n <= 13611936465570593
              exact RamareSaouter2003.prime_interval_nat_ladder_c05522 n (by omega) (by omega)
        · -- n <= 13573506119811839
          rcases Nat.lt_or_ge 13496971713425257 n with h10 | h10
          · -- n > 13496971713425257
            rcases Nat.lt_or_ge 13535184756202957 n with h12 | h12
            · -- n > 13535184756202957
              exact RamareSaouter2003.prime_interval_nat_ladder_c05521 n (by omega) (by omega)
            · -- n <= 13535184756202957
              exact RamareSaouter2003.prime_interval_nat_ladder_c05520 n (by omega) (by omega)
          · -- n <= 13496971713425257
            exact RamareSaouter2003.prime_interval_nat_ladder_c05519 n (by omega) (by omega)
      · -- n <= 13458865815480167
        rcases Nat.lt_or_ge 13345197104325551 n with h8 | h8
        · -- n > 13345197104325551
          rcases Nat.lt_or_ge 13382980132719749 n with h10 | h10
          · -- n > 13382980132719749
            rcases Nat.lt_or_ge 13420868237511859 n with h12 | h12
            · -- n > 13420868237511859
              exact RamareSaouter2003.prime_interval_nat_ladder_c05518 n (by omega) (by omega)
            · -- n <= 13420868237511859
              exact RamareSaouter2003.prime_interval_nat_ladder_c05517 n (by omega) (by omega)
          · -- n <= 13382980132719749
            exact RamareSaouter2003.prime_interval_nat_ladder_c05516 n (by omega) (by omega)
        · -- n <= 13345197104325551
          rcases Nat.lt_or_ge 13269958318847609 n with h10 | h10
          · -- n > 13269958318847609
            rcases Nat.lt_or_ge 13307526785431523 n with h12 | h12
            · -- n > 13307526785431523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05515 n (by omega) (by omega)
            · -- n <= 13307526785431523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05514 n (by omega) (by omega)
          · -- n <= 13269958318847609
            exact RamareSaouter2003.prime_interval_nat_ladder_c05513 n (by omega) (by omega)
    · -- n <= 13232493570143149
      rcases Nat.lt_or_ge 13009932081098531 n with h6 | h6
      · -- n > 13009932081098531
        rcases Nat.lt_or_ge 13120743086825021 n with h8 | h8
        · -- n > 13120743086825021
          rcases Nat.lt_or_ge 13157884918295077 n with h10 | h10
          · -- n > 13157884918295077
            rcases Nat.lt_or_ge 13195135770278507 n with h12 | h12
            · -- n > 13195135770278507
              exact RamareSaouter2003.prime_interval_nat_ladder_c05512 n (by omega) (by omega)
            · -- n <= 13195135770278507
              exact RamareSaouter2003.prime_interval_nat_ladder_c05511 n (by omega) (by omega)
          · -- n <= 13157884918295077
            exact RamareSaouter2003.prime_interval_nat_ladder_c05510 n (by omega) (by omega)
        · -- n <= 13120743086825021
          rcases Nat.lt_or_ge 13046764937757851 n with h10 | h10
          · -- n > 13046764937757851
            rcases Nat.lt_or_ge 13083704308227461 n with h12 | h12
            · -- n > 13083704308227461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05509 n (by omega) (by omega)
            · -- n <= 13083704308227461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05508 n (by omega) (by omega)
          · -- n <= 13046764937757851
            exact RamareSaouter2003.prime_interval_nat_ladder_c05507 n (by omega) (by omega)
      · -- n <= 13009932081098531
        rcases Nat.lt_or_ge 12900064140292073 n with h8 | h8
        · -- n > 12900064140292073
          rcases Nat.lt_or_ge 12936585430130611 n with h10 | h10
          · -- n > 12936585430130611
            rcases Nat.lt_or_ge 12973201391712797 n with h12 | h12
            · -- n > 12973201391712797
              exact RamareSaouter2003.prime_interval_nat_ladder_c05506 n (by omega) (by omega)
            · -- n <= 12973201391712797
              exact RamareSaouter2003.prime_interval_nat_ladder_c05505 n (by omega) (by omega)
          · -- n <= 12936585430130611
            exact RamareSaouter2003.prime_interval_nat_ladder_c05504 n (by omega) (by omega)
        · -- n <= 12900064140292073
          rcases Nat.lt_or_ge 12827341568790487 n with h10 | h10
          · -- n > 12827341568790487
            rcases Nat.lt_or_ge 12863653685173097 n with h12 | h12
            · -- n > 12863653685173097
              exact RamareSaouter2003.prime_interval_nat_ladder_c05503 n (by omega) (by omega)
            · -- n <= 12863653685173097
              exact RamareSaouter2003.prime_interval_nat_ladder_c05502 n (by omega) (by omega)
          · -- n <= 12827341568790487
            exact RamareSaouter2003.prime_interval_nat_ladder_c05501 n (by omega) (by omega)
