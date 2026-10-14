-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T23:11:58.385822+00:00
-- url     : https://prove2.me/submissions/558d6d5a-305b-4744-9163-4f782d660aec

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02650

theorem solution (n : Nat)
    (hn : 5645912403713 < n) (hupper : n <= 6388603926769) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 6005788720237 n with h2 | h2
  · -- n > 6005788720237
    rcases Nat.lt_or_ge 6186589337587 n with h4 | h4
    · -- n > 6186589337587
      rcases Nat.lt_or_ge 6279020603497 n with h6 | h6
      · -- n > 6279020603497
        rcases Nat.lt_or_ge 6325752820711 n with h8 | h8
        · -- n > 6325752820711
          rcases Nat.lt_or_ge 6357100699931 n with h10 | h10
          · -- n > 6357100699931
            rcases Nat.lt_or_ge 6372832846903 n with h12 | h12
            · -- n > 6372832846903
              exact RamareSaouter2003.prime_interval_nat_ladder_c02650 n (by omega) (by omega)
            · -- n <= 6372832846903
              exact RamareSaouter2003.prime_interval_nat_ladder_c02649 n (by omega) (by omega)
          · -- n <= 6357100699931
            rcases Nat.lt_or_ge 6341407389839 n with h12 | h12
            · -- n > 6341407389839
              exact RamareSaouter2003.prime_interval_nat_ladder_c02648 n (by omega) (by omega)
            · -- n <= 6341407389839
              exact RamareSaouter2003.prime_interval_nat_ladder_c02647 n (by omega) (by omega)
        · -- n <= 6325752820711
          rcases Nat.lt_or_ge 6294559522781 n with h10 | h10
          · -- n > 6294559522781
            rcases Nat.lt_or_ge 6310136896787 n with h12 | h12
            · -- n > 6310136896787
              exact RamareSaouter2003.prime_interval_nat_ladder_c02646 n (by omega) (by omega)
            · -- n <= 6310136896787
              exact RamareSaouter2003.prime_interval_nat_ladder_c02645 n (by omega) (by omega)
          · -- n <= 6294559522781
            exact RamareSaouter2003.prime_interval_nat_ladder_c02644 n (by omega) (by omega)
      · -- n <= 6279020603497
        rcases Nat.lt_or_ge 6232633625903 n with h8 | h8
        · -- n > 6232633625903
          rcases Nat.lt_or_ge 6248057749669 n with h10 | h10
          · -- n > 6248057749669
            rcases Nat.lt_or_ge 6263520043969 n with h12 | h12
            · -- n > 6263520043969
              exact RamareSaouter2003.prime_interval_nat_ladder_c02643 n (by omega) (by omega)
            · -- n <= 6263520043969
              exact RamareSaouter2003.prime_interval_nat_ladder_c02642 n (by omega) (by omega)
          · -- n <= 6248057749669
            exact RamareSaouter2003.prime_interval_nat_ladder_c02641 n (by omega) (by omega)
        · -- n <= 6232633625903
          rcases Nat.lt_or_ge 6201899513699 n with h10 | h10
          · -- n > 6201899513699
            rcases Nat.lt_or_ge 6217247578537 n with h12 | h12
            · -- n > 6217247578537
              exact RamareSaouter2003.prime_interval_nat_ladder_c02640 n (by omega) (by omega)
            · -- n <= 6217247578537
              exact RamareSaouter2003.prime_interval_nat_ladder_c02639 n (by omega) (by omega)
          · -- n <= 6201899513699
            exact RamareSaouter2003.prime_interval_nat_ladder_c02638 n (by omega) (by omega)
    · -- n <= 6186589337587
      rcases Nat.lt_or_ge 6095518719593 n with h6 | h6
      · -- n > 6095518719593
        rcases Nat.lt_or_ge 6140885206283 n with h8 | h8
        · -- n > 6140885206283
          rcases Nat.lt_or_ge 6156082276957 n with h10 | h10
          · -- n > 6156082276957
            rcases Nat.lt_or_ge 6171316956373 n with h12 | h12
            · -- n > 6171316956373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02637 n (by omega) (by omega)
            · -- n <= 6171316956373
              exact RamareSaouter2003.prime_interval_nat_ladder_c02636 n (by omega) (by omega)
          · -- n <= 6156082276957
            exact RamareSaouter2003.prime_interval_nat_ladder_c02635 n (by omega) (by omega)
        · -- n <= 6140885206283
          rcases Nat.lt_or_ge 6110603520179 n with h10 | h10
          · -- n > 6110603520179
            rcases Nat.lt_or_ge 6125725651553 n with h12 | h12
            · -- n > 6125725651553
              exact RamareSaouter2003.prime_interval_nat_ladder_c02634 n (by omega) (by omega)
            · -- n <= 6125725651553
              exact RamareSaouter2003.prime_interval_nat_ladder_c02633 n (by omega) (by omega)
          · -- n <= 6110603520179
            exact RamareSaouter2003.prime_interval_nat_ladder_c02632 n (by omega) (by omega)
      · -- n <= 6095518719593
        rcases Nat.lt_or_ge 6050487382853 n with h8 | h8
        · -- n > 6050487382853
          rcases Nat.lt_or_ge 6065460742753 n with h10 | h10
          · -- n > 6065460742753
            rcases Nat.lt_or_ge 6080471157769 n with h12 | h12
            · -- n > 6080471157769
              exact RamareSaouter2003.prime_interval_nat_ladder_c02631 n (by omega) (by omega)
            · -- n <= 6080471157769
              exact RamareSaouter2003.prime_interval_nat_ladder_c02630 n (by omega) (by omega)
          · -- n <= 6065460742753
            exact RamareSaouter2003.prime_interval_nat_ladder_c02629 n (by omega) (by omega)
        · -- n <= 6050487382853
          rcases Nat.lt_or_ge 6020651462747 n with h10 | h10
          · -- n > 6020651462747
            rcases Nat.lt_or_ge 6035550986587 n with h12 | h12
            · -- n > 6035550986587
              exact RamareSaouter2003.prime_interval_nat_ladder_c02628 n (by omega) (by omega)
            · -- n <= 6035550986587
              exact RamareSaouter2003.prime_interval_nat_ladder_c02627 n (by omega) (by omega)
          · -- n <= 6020651462747
            exact RamareSaouter2003.prime_interval_nat_ladder_c02626 n (by omega) (by omega)
  · -- n <= 6005788720237
    rcases Nat.lt_or_ge 5815879162993 n with h4 | h4
    · -- n > 5815879162993
      rcases Nat.lt_or_ge 5902771802243 n with h6 | h6
      · -- n > 5902771802243
        rcases Nat.lt_or_ge 5946703751477 n with h8 | h8
        · -- n > 5946703751477
          rcases Nat.lt_or_ge 5976173216537 n with h10 | h10
          · -- n > 5976173216537
            rcases Nat.lt_or_ge 5990962668329 n with h12 | h12
            · -- n > 5990962668329
              exact RamareSaouter2003.prime_interval_nat_ladder_c02625 n (by omega) (by omega)
            · -- n <= 5990962668329
              exact RamareSaouter2003.prime_interval_nat_ladder_c02624 n (by omega) (by omega)
          · -- n <= 5976173216537
            rcases Nat.lt_or_ge 5961420274261 n with h12 | h12
            · -- n > 5961420274261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02623 n (by omega) (by omega)
            · -- n <= 5961420274261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02622 n (by omega) (by omega)
        · -- n <= 5946703751477
          rcases Nat.lt_or_ge 5917379605073 n with h10 | h10
          · -- n > 5917379605073
            rcases Nat.lt_or_ge 5932023558323 n with h12 | h12
            · -- n > 5932023558323
              exact RamareSaouter2003.prime_interval_nat_ladder_c02621 n (by omega) (by omega)
            · -- n <= 5932023558323
              exact RamareSaouter2003.prime_interval_nat_ladder_c02620 n (by omega) (by omega)
          · -- n <= 5917379605073
            exact RamareSaouter2003.prime_interval_nat_ladder_c02619 n (by omega) (by omega)
      · -- n <= 5902771802243
        rcases Nat.lt_or_ge 5859164405377 n with h8 | h8
        · -- n > 5859164405377
          rcases Nat.lt_or_ge 5873664291379 n with h10 | h10
          · -- n > 5873664291379
            rcases Nat.lt_or_ge 5888200060637 n with h12 | h12
            · -- n > 5888200060637
              exact RamareSaouter2003.prime_interval_nat_ladder_c02618 n (by omega) (by omega)
            · -- n <= 5888200060637
              exact RamareSaouter2003.prime_interval_nat_ladder_c02617 n (by omega) (by omega)
          · -- n <= 5873664291379
            exact RamareSaouter2003.prime_interval_nat_ladder_c02616 n (by omega) (by omega)
        · -- n <= 5859164405377
          rcases Nat.lt_or_ge 5830271929459 n with h10 | h10
          · -- n > 5830271929459
            rcases Nat.lt_or_ge 5844700314191 n with h12 | h12
            · -- n > 5844700314191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02615 n (by omega) (by omega)
            · -- n <= 5844700314191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02614 n (by omega) (by omega)
          · -- n <= 5830271929459
            exact RamareSaouter2003.prime_interval_nat_ladder_c02613 n (by omega) (by omega)
    · -- n <= 5815879162993
      rcases Nat.lt_or_ge 5730265639949 n with h6 | h6
      · -- n > 5730265639949
        rcases Nat.lt_or_ge 5772913695473 n with h8 | h8
        · -- n > 5772913695473
          rcases Nat.lt_or_ge 5787200133751 n with h10 | h10
          · -- n > 5787200133751
            rcases Nat.lt_or_ge 5801521927081 n with h12 | h12
            · -- n > 5801521927081
              exact RamareSaouter2003.prime_interval_nat_ladder_c02612 n (by omega) (by omega)
            · -- n <= 5801521927081
              exact RamareSaouter2003.prime_interval_nat_ladder_c02611 n (by omega) (by omega)
          · -- n <= 5787200133751
            exact RamareSaouter2003.prime_interval_nat_ladder_c02610 n (by omega) (by omega)
        · -- n <= 5772913695473
          rcases Nat.lt_or_ge 5744446535539 n with h10 | h10
          · -- n > 5744446535539
            rcases Nat.lt_or_ge 5758662525107 n with h12 | h12
            · -- n > 5758662525107
              exact RamareSaouter2003.prime_interval_nat_ladder_c02609 n (by omega) (by omega)
            · -- n <= 5758662525107
              exact RamareSaouter2003.prime_interval_nat_ladder_c02608 n (by omega) (by omega)
          · -- n <= 5744446535539
            exact RamareSaouter2003.prime_interval_nat_ladder_c02607 n (by omega) (by omega)
      · -- n <= 5730265639949
        rcases Nat.lt_or_ge 5687932651837 n with h8 | h8
        · -- n > 5687932651837
          rcases Nat.lt_or_ge 5702008784449 n with h10 | h10
          · -- n > 5702008784449
            rcases Nat.lt_or_ge 5716119751751 n with h12 | h12
            · -- n > 5716119751751
              exact RamareSaouter2003.prime_interval_nat_ladder_c02606 n (by omega) (by omega)
            · -- n <= 5716119751751
              exact RamareSaouter2003.prime_interval_nat_ladder_c02605 n (by omega) (by omega)
          · -- n <= 5702008784449
            exact RamareSaouter2003.prime_interval_nat_ladder_c02604 n (by omega) (by omega)
        · -- n <= 5687932651837
          rcases Nat.lt_or_ge 5659884547007 n with h10 | h10
          · -- n > 5659884547007
            rcases Nat.lt_or_ge 5673891267953 n with h12 | h12
            · -- n > 5673891267953
              exact RamareSaouter2003.prime_interval_nat_ladder_c02603 n (by omega) (by omega)
            · -- n <= 5673891267953
              exact RamareSaouter2003.prime_interval_nat_ladder_c02602 n (by omega) (by omega)
          · -- n <= 5659884547007
            exact RamareSaouter2003.prime_interval_nat_ladder_c02601 n (by omega) (by omega)
