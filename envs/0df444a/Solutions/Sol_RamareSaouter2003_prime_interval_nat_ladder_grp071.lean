-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:27:22.010995+00:00
-- url     : https://prove2.me/submissions/62050e0b-a034-45dc-b51c-c7c15f8e30e6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03550

theorem solution (n : Nat)
    (hn : 52218819183697 < n) (hupper : n <= 59087943554933) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 55547300927707 n with h2 | h2
  · -- n > 55547300927707
    rcases Nat.lt_or_ge 57219518647121 n with h4 | h4
    · -- n > 57219518647121
      rcases Nat.lt_or_ge 58074411753913 n with h6 | h6
      · -- n > 58074411753913
        rcases Nat.lt_or_ge 58506636173191 n with h8 | h8
        · -- n > 58506636173191
          rcases Nat.lt_or_ge 58796571462929 n with h10 | h10
          · -- n > 58796571462929
            rcases Nat.lt_or_ge 58942077464401 n with h12 | h12
            · -- n > 58942077464401
              exact RamareSaouter2003.prime_interval_nat_ladder_c03550 n (by omega) (by omega)
            · -- n <= 58942077464401
              exact RamareSaouter2003.prime_interval_nat_ladder_c03549 n (by omega) (by omega)
          · -- n <= 58796571462929
            rcases Nat.lt_or_ge 58651424661413 n with h12 | h12
            · -- n > 58651424661413
              exact RamareSaouter2003.prime_interval_nat_ladder_c03548 n (by omega) (by omega)
            · -- n <= 58651424661413
              exact RamareSaouter2003.prime_interval_nat_ladder_c03547 n (by omega) (by omega)
        · -- n <= 58506636173191
          rcases Nat.lt_or_ge 58218130600711 n with h10 | h10
          · -- n > 58218130600711
            rcases Nat.lt_or_ge 58362205113733 n with h12 | h12
            · -- n > 58362205113733
              exact RamareSaouter2003.prime_interval_nat_ladder_c03546 n (by omega) (by omega)
            · -- n <= 58362205113733
              exact RamareSaouter2003.prime_interval_nat_ladder_c03545 n (by omega) (by omega)
          · -- n <= 58218130600711
            exact RamareSaouter2003.prime_interval_nat_ladder_c03544 n (by omega) (by omega)
      · -- n <= 58074411753913
        rcases Nat.lt_or_ge 57645380441713 n with h8 | h8
        · -- n > 57645380441713
          rcases Nat.lt_or_ge 57788037549233 n with h10 | h10
          · -- n > 57788037549233
            rcases Nat.lt_or_ge 57931047695441 n with h12 | h12
            · -- n > 57931047695441
              exact RamareSaouter2003.prime_interval_nat_ladder_c03543 n (by omega) (by omega)
            · -- n <= 57931047695441
              exact RamareSaouter2003.prime_interval_nat_ladder_c03542 n (by omega) (by omega)
          · -- n <= 57788037549233
            exact RamareSaouter2003.prime_interval_nat_ladder_c03541 n (by omega) (by omega)
        · -- n <= 57645380441713
          rcases Nat.lt_or_ge 57361121858993 n with h10 | h10
          · -- n > 57361121858993
            rcases Nat.lt_or_ge 57503075501453 n with h12 | h12
            · -- n > 57503075501453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03540 n (by omega) (by omega)
            · -- n <= 57503075501453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03539 n (by omega) (by omega)
          · -- n <= 57361121858993
            exact RamareSaouter2003.prime_interval_nat_ladder_c03538 n (by omega) (by omega)
    · -- n <= 57219518647121
      rcases Nat.lt_or_ge 56377210122763 n with h6 | h6
      · -- n > 56377210122763
        rcases Nat.lt_or_ge 56796802954897 n with h8 | h8
        · -- n > 56796802954897
          rcases Nat.lt_or_ge 56937360057001 n with h10 | h10
          · -- n > 56937360057001
            rcases Nat.lt_or_ge 57078265000769 n with h12 | h12
            · -- n > 57078265000769
              exact RamareSaouter2003.prime_interval_nat_ladder_c03537 n (by omega) (by omega)
            · -- n <= 57078265000769
              exact RamareSaouter2003.prime_interval_nat_ladder_c03536 n (by omega) (by omega)
          · -- n <= 56937360057001
            exact RamareSaouter2003.prime_interval_nat_ladder_c03535 n (by omega) (by omega)
        · -- n <= 56796802954897
          rcases Nat.lt_or_ge 56516728843241 n with h10 | h10
          · -- n > 56516728843241
            rcases Nat.lt_or_ge 56656592835839 n with h12 | h12
            · -- n > 56656592835839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03534 n (by omega) (by omega)
            · -- n <= 56656592835839
              exact RamareSaouter2003.prime_interval_nat_ladder_c03533 n (by omega) (by omega)
          · -- n <= 56516728843241
            exact RamareSaouter2003.prime_interval_nat_ladder_c03532 n (by omega) (by omega)
      · -- n <= 56377210122763
        rcases Nat.lt_or_ge 55960717080361 n with h8 | h8
        · -- n > 55960717080361
          rcases Nat.lt_or_ge 56099205090541 n with h10 | h10
          · -- n > 56099205090541
            rcases Nat.lt_or_ge 56238035821999 n with h12 | h12
            · -- n > 56238035821999
              exact RamareSaouter2003.prime_interval_nat_ladder_c03531 n (by omega) (by omega)
            · -- n <= 56238035821999
              exact RamareSaouter2003.prime_interval_nat_ladder_c03530 n (by omega) (by omega)
          · -- n <= 56099205090541
            exact RamareSaouter2003.prime_interval_nat_ladder_c03529 n (by omega) (by omega)
        · -- n <= 55960717080361
          rcases Nat.lt_or_ge 55684765841927 n with h10 | h10
          · -- n > 55684765841927
            rcases Nat.lt_or_ge 55822570945579 n with h12 | h12
            · -- n > 55822570945579
              exact RamareSaouter2003.prime_interval_nat_ladder_c03528 n (by omega) (by omega)
            · -- n <= 55822570945579
              exact RamareSaouter2003.prime_interval_nat_ladder_c03527 n (by omega) (by omega)
          · -- n <= 55684765841927
            exact RamareSaouter2003.prime_interval_nat_ladder_c03526 n (by omega) (by omega)
  · -- n <= 55547300927707
    rcases Nat.lt_or_ge 53790834983671 n with h4 | h4
    · -- n > 53790834983671
      rcases Nat.lt_or_ge 54594501548551 n with h6 | h6
      · -- n > 54594501548551
        rcases Nat.lt_or_ge 55000826399917 n with h8 | h8
        · -- n > 55000826399917
          rcases Nat.lt_or_ge 55273388310281 n with h10 | h10
          · -- n > 55273388310281
            rcases Nat.lt_or_ge 55410175363031 n with h12 | h12
            · -- n > 55410175363031
              exact RamareSaouter2003.prime_interval_nat_ladder_c03525 n (by omega) (by omega)
            · -- n <= 55410175363031
              exact RamareSaouter2003.prime_interval_nat_ladder_c03524 n (by omega) (by omega)
          · -- n <= 55273388310281
            rcases Nat.lt_or_ge 55136938933729 n with h12 | h12
            · -- n > 55136938933729
              exact RamareSaouter2003.prime_interval_nat_ladder_c03523 n (by omega) (by omega)
            · -- n <= 55136938933729
              exact RamareSaouter2003.prime_interval_nat_ladder_c03522 n (by omega) (by omega)
        · -- n <= 55000826399917
          rcases Nat.lt_or_ge 54729608535751 n with h10 | h10
          · -- n > 54729608535751
            rcases Nat.lt_or_ge 54865049877037 n with h12 | h12
            · -- n > 54865049877037
              exact RamareSaouter2003.prime_interval_nat_ladder_c03521 n (by omega) (by omega)
            · -- n <= 54865049877037
              exact RamareSaouter2003.prime_interval_nat_ladder_c03520 n (by omega) (by omega)
          · -- n <= 54729608535751
            exact RamareSaouter2003.prime_interval_nat_ladder_c03519 n (by omega) (by omega)
      · -- n <= 54594501548551
        rcases Nat.lt_or_ge 54191178468649 n with h8 | h8
        · -- n > 54191178468649
          rcases Nat.lt_or_ge 54325287337301 n with h10 | h10
          · -- n > 54325287337301
            rcases Nat.lt_or_ge 54459728090191 n with h12 | h12
            · -- n > 54459728090191
              exact RamareSaouter2003.prime_interval_nat_ladder_c03518 n (by omega) (by omega)
            · -- n <= 54459728090191
              exact RamareSaouter2003.prime_interval_nat_ladder_c03517 n (by omega) (by omega)
          · -- n <= 54325287337301
            exact RamareSaouter2003.prime_interval_nat_ladder_c03516 n (by omega) (by omega)
        · -- n <= 54191178468649
          rcases Nat.lt_or_ge 53923953107911 n with h10 | h10
          · -- n > 53923953107911
            rcases Nat.lt_or_ge 54057400664633 n with h12 | h12
            · -- n > 54057400664633
              exact RamareSaouter2003.prime_interval_nat_ladder_c03515 n (by omega) (by omega)
            · -- n <= 54057400664633
              exact RamareSaouter2003.prime_interval_nat_ladder_c03514 n (by omega) (by omega)
          · -- n <= 53923953107911
            exact RamareSaouter2003.prime_interval_nat_ladder_c03513 n (by omega) (by omega)
    · -- n <= 53790834983671
      rcases Nat.lt_or_ge 52998998912611 n with h6 | h6
      · -- n > 52998998912611
        rcases Nat.lt_or_ge 53393449081471 n with h8 | h8
        · -- n > 53393449081471
          rcases Nat.lt_or_ge 53525583780679 n with h10 | h10
          · -- n > 53525583780679
            rcases Nat.lt_or_ge 53658045478321 n with h12 | h12
            · -- n > 53658045478321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03512 n (by omega) (by omega)
            · -- n <= 53658045478321
              exact RamareSaouter2003.prime_interval_nat_ladder_c03511 n (by omega) (by omega)
          · -- n <= 53525583780679
            exact RamareSaouter2003.prime_interval_nat_ladder_c03510 n (by omega) (by omega)
        · -- n <= 53393449081471
          rcases Nat.lt_or_ge 53130157451747 n with h10 | h10
          · -- n > 53130157451747
            rcases Nat.lt_or_ge 53261640573523 n with h12 | h12
            · -- n > 53261640573523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03509 n (by omega) (by omega)
            · -- n <= 53261640573523
              exact RamareSaouter2003.prime_interval_nat_ladder_c03508 n (by omega) (by omega)
          · -- n <= 53130157451747
            exact RamareSaouter2003.prime_interval_nat_ladder_c03507 n (by omega) (by omega)
      · -- n <= 52998998912611
        rcases Nat.lt_or_ge 52607462789417 n with h8 | h8
        · -- n > 52607462789417
          rcases Nat.lt_or_ge 52737652379701 n with h10 | h10
          · -- n > 52737652379701
            rcases Nat.lt_or_ge 52868164155049 n with h12 | h12
            · -- n > 52868164155049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03506 n (by omega) (by omega)
            · -- n <= 52868164155049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03505 n (by omega) (by omega)
          · -- n <= 52737652379701
            exact RamareSaouter2003.prime_interval_nat_ladder_c03504 n (by omega) (by omega)
        · -- n <= 52607462789417
          rcases Nat.lt_or_ge 52348046983723 n with h10 | h10
          · -- n > 52348046983723
            rcases Nat.lt_or_ge 52477594588577 n with h12 | h12
            · -- n > 52477594588577
              exact RamareSaouter2003.prime_interval_nat_ladder_c03503 n (by omega) (by omega)
            · -- n <= 52477594588577
              exact RamareSaouter2003.prime_interval_nat_ladder_c03502 n (by omega) (by omega)
          · -- n <= 52348046983723
            exact RamareSaouter2003.prime_interval_nat_ladder_c03501 n (by omega) (by omega)
