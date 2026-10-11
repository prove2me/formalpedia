-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T22:10:26.65154+00:00
-- url     : https://prove2.me/submissions/480cf6c3-ebcd-4264-bc6b-f40b129c2949

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00700

theorem solution (n : Nat)
    (hn : 45340845131 < n) (hupper : n <= 50809618939) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 47995645441 n with h2 | h2
  · -- n > 47995645441
    rcases Nat.lt_or_ge 49325900831 n with h4 | h4
    · -- n > 49325900831
      rcases Nat.lt_or_ge 50005108369 n with h6 | h6
      · -- n > 50005108369
        rcases Nat.lt_or_ge 50348291437 n with h8 | h8
        · -- n > 50348291437
          rcases Nat.lt_or_ge 50578417321 n with h10 | h10
          · -- n > 50578417321
            rcases Nat.lt_or_ge 50693883367 n with h12 | h12
            · -- n > 50693883367
              exact RamareSaouter2003.prime_interval_nat_ladder_c00700 n (by omega) (by omega)
            · -- n <= 50693883367
              exact RamareSaouter2003.prime_interval_nat_ladder_c00699 n (by omega) (by omega)
          · -- n <= 50578417321
            rcases Nat.lt_or_ge 50463220211 n with h12 | h12
            · -- n > 50463220211
              exact RamareSaouter2003.prime_interval_nat_ladder_c00698 n (by omega) (by omega)
            · -- n <= 50463220211
              exact RamareSaouter2003.prime_interval_nat_ladder_c00697 n (by omega) (by omega)
        · -- n <= 50348291437
          rcases Nat.lt_or_ge 50119236107 n with h10 | h10
          · -- n > 50119236107
            rcases Nat.lt_or_ge 50233630253 n with h12 | h12
            · -- n > 50233630253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00696 n (by omega) (by omega)
            · -- n <= 50233630253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00695 n (by omega) (by omega)
          · -- n <= 50119236107
            exact RamareSaouter2003.prime_interval_nat_ladder_c00694 n (by omega) (by omega)
      · -- n <= 50005108369
        rcases Nat.lt_or_ge 49664317193 n with h8 | h8
        · -- n > 49664317193
          rcases Nat.lt_or_ge 49777649521 n with h10 | h10
          · -- n > 49777649521
            rcases Nat.lt_or_ge 49891246369 n with h12 | h12
            · -- n > 49891246369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00693 n (by omega) (by omega)
            · -- n <= 49891246369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00692 n (by omega) (by omega)
          · -- n <= 49777649521
            exact RamareSaouter2003.prime_interval_nat_ladder_c00691 n (by omega) (by omega)
        · -- n <= 49664317193
          rcases Nat.lt_or_ge 49438443367 n with h10 | h10
          · -- n > 49438443367
            rcases Nat.lt_or_ge 49551248623 n with h12 | h12
            · -- n > 49551248623
              exact RamareSaouter2003.prime_interval_nat_ladder_c00690 n (by omega) (by omega)
            · -- n <= 49551248623
              exact RamareSaouter2003.prime_interval_nat_ladder_c00689 n (by omega) (by omega)
          · -- n <= 49438443367
            exact RamareSaouter2003.prime_interval_nat_ladder_c00688 n (by omega) (by omega)
    · -- n <= 49325900831
      rcases Nat.lt_or_ge 48656124373 n with h6 | h6
      · -- n > 48656124373
        rcases Nat.lt_or_ge 48989842061 n with h8 | h8
        · -- n > 48989842061
          rcases Nat.lt_or_ge 49101600721 n with h10 | h10
          · -- n > 49101600721
            rcases Nat.lt_or_ge 49213620101 n with h12 | h12
            · -- n > 49213620101
              exact RamareSaouter2003.prime_interval_nat_ladder_c00687 n (by omega) (by omega)
            · -- n <= 49213620101
              exact RamareSaouter2003.prime_interval_nat_ladder_c00686 n (by omega) (by omega)
          · -- n <= 49101600721
            exact RamareSaouter2003.prime_interval_nat_ladder_c00685 n (by omega) (by omega)
        · -- n <= 48989842061
          rcases Nat.lt_or_ge 48767104513 n with h10 | h10
          · -- n > 48767104513
            rcases Nat.lt_or_ge 48878343551 n with h12 | h12
            · -- n > 48878343551
              exact RamareSaouter2003.prime_interval_nat_ladder_c00684 n (by omega) (by omega)
            · -- n <= 48878343551
              exact RamareSaouter2003.prime_interval_nat_ladder_c00683 n (by omega) (by omega)
          · -- n <= 48767104513
            exact RamareSaouter2003.prime_interval_nat_ladder_c00682 n (by omega) (by omega)
      · -- n <= 48656124373
        rcases Nat.lt_or_ge 48324730969 n with h8 | h8
        · -- n > 48324730969
          rcases Nat.lt_or_ge 48434938199 n with h10 | h10
          · -- n > 48434938199
            rcases Nat.lt_or_ge 48545402471 n with h12 | h12
            · -- n > 48545402471
              exact RamareSaouter2003.prime_interval_nat_ladder_c00681 n (by omega) (by omega)
            · -- n <= 48545402471
              exact RamareSaouter2003.prime_interval_nat_ladder_c00680 n (by omega) (by omega)
          · -- n <= 48434938199
            exact RamareSaouter2003.prime_interval_nat_ladder_c00679 n (by omega) (by omega)
        · -- n <= 48324730969
          rcases Nat.lt_or_ge 48105085211 n with h10 | h10
          · -- n > 48105085211
            rcases Nat.lt_or_ge 48214780157 n with h12 | h12
            · -- n > 48214780157
              exact RamareSaouter2003.prime_interval_nat_ladder_c00678 n (by omega) (by omega)
            · -- n <= 48214780157
              exact RamareSaouter2003.prime_interval_nat_ladder_c00677 n (by omega) (by omega)
          · -- n <= 48105085211
            exact RamareSaouter2003.prime_interval_nat_ladder_c00676 n (by omega) (by omega)
  · -- n <= 47995645441
    rcases Nat.lt_or_ge 46595878339 n with h4 | h4
    · -- n > 46595878339
      rcases Nat.lt_or_ge 47236662047 n with h6 | h6
      · -- n > 47236662047
        rcases Nat.lt_or_ge 47560426321 n with h8 | h8
        · -- n > 47560426321
          rcases Nat.lt_or_ge 47777529103 n with h10 | h10
          · -- n > 47777529103
            rcases Nat.lt_or_ge 47886460301 n with h12 | h12
            · -- n > 47886460301
              exact RamareSaouter2003.prime_interval_nat_ladder_c00675 n (by omega) (by omega)
            · -- n <= 47886460301
              exact RamareSaouter2003.prime_interval_nat_ladder_c00674 n (by omega) (by omega)
          · -- n <= 47777529103
            rcases Nat.lt_or_ge 47668851301 n with h12 | h12
            · -- n > 47668851301
              exact RamareSaouter2003.prime_interval_nat_ladder_c00673 n (by omega) (by omega)
            · -- n <= 47668851301
              exact RamareSaouter2003.prime_interval_nat_ladder_c00672 n (by omega) (by omega)
        · -- n <= 47560426321
          rcases Nat.lt_or_ge 47344332283 n with h10 | h10
          · -- n > 47344332283
            rcases Nat.lt_or_ge 47452253509 n with h12 | h12
            · -- n > 47452253509
              exact RamareSaouter2003.prime_interval_nat_ladder_c00671 n (by omega) (by omega)
            · -- n <= 47452253509
              exact RamareSaouter2003.prime_interval_nat_ladder_c00670 n (by omega) (by omega)
          · -- n <= 47344332283
            exact RamareSaouter2003.prime_interval_nat_ladder_c00669 n (by omega) (by omega)
      · -- n <= 47236662047
        rcases Nat.lt_or_ge 46915151431 n with h8 | h8
        · -- n > 46915151431
          rcases Nat.lt_or_ge 47022072221 n with h10 | h10
          · -- n > 47022072221
            rcases Nat.lt_or_ge 47129242249 n with h12 | h12
            · -- n > 47129242249
              exact RamareSaouter2003.prime_interval_nat_ladder_c00668 n (by omega) (by omega)
            · -- n <= 47129242249
              exact RamareSaouter2003.prime_interval_nat_ladder_c00667 n (by omega) (by omega)
          · -- n <= 47022072221
            exact RamareSaouter2003.prime_interval_nat_ladder_c00666 n (by omega) (by omega)
        · -- n <= 46915151431
          rcases Nat.lt_or_ge 46702055077 n with h10 | h10
          · -- n > 46702055077
            rcases Nat.lt_or_ge 46808479271 n with h12 | h12
            · -- n > 46808479271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00665 n (by omega) (by omega)
            · -- n <= 46808479271
              exact RamareSaouter2003.prime_interval_nat_ladder_c00664 n (by omega) (by omega)
          · -- n <= 46702055077
            exact RamareSaouter2003.prime_interval_nat_ladder_c00663 n (by omega) (by omega)
    · -- n <= 46595878339
      rcases Nat.lt_or_ge 45963981439 n with h6 | h6
      · -- n > 45963981439
        rcases Nat.lt_or_ge 46278826949 n with h8 | h8
        · -- n > 46278826949
          rcases Nat.lt_or_ge 46384264867 n with h10 | h10
          · -- n > 46384264867
            rcases Nat.lt_or_ge 46489948487 n with h12 | h12
            · -- n > 46489948487
              exact RamareSaouter2003.prime_interval_nat_ladder_c00662 n (by omega) (by omega)
            · -- n <= 46489948487
              exact RamareSaouter2003.prime_interval_nat_ladder_c00661 n (by omega) (by omega)
          · -- n <= 46384264867
            exact RamareSaouter2003.prime_interval_nat_ladder_c00660 n (by omega) (by omega)
        · -- n <= 46278826949
          rcases Nat.lt_or_ge 46068685807 n with h10 | h10
          · -- n > 46068685807
            rcases Nat.lt_or_ge 46173634151 n with h12 | h12
            · -- n > 46173634151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00659 n (by omega) (by omega)
            · -- n <= 46173634151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00658 n (by omega) (by omega)
          · -- n <= 46068685807
            exact RamareSaouter2003.prime_interval_nat_ladder_c00657 n (by omega) (by omega)
      · -- n <= 45963981439
        rcases Nat.lt_or_ge 45651325999 n with h8 | h8
        · -- n > 45651325999
          rcases Nat.lt_or_ge 45755302079 n with h10 | h10
          · -- n > 45755302079
            rcases Nat.lt_or_ge 45859520363 n with h12 | h12
            · -- n > 45859520363
              exact RamareSaouter2003.prime_interval_nat_ladder_c00656 n (by omega) (by omega)
            · -- n <= 45859520363
              exact RamareSaouter2003.prime_interval_nat_ladder_c00655 n (by omega) (by omega)
          · -- n <= 45755302079
            exact RamareSaouter2003.prime_interval_nat_ladder_c00654 n (by omega) (by omega)
        · -- n <= 45651325999
          rcases Nat.lt_or_ge 45444098093 n with h10 | h10
          · -- n > 45444098093
            rcases Nat.lt_or_ge 45547591517 n with h12 | h12
            · -- n > 45547591517
              exact RamareSaouter2003.prime_interval_nat_ladder_c00653 n (by omega) (by omega)
            · -- n <= 45547591517
              exact RamareSaouter2003.prime_interval_nat_ladder_c00652 n (by omega) (by omega)
          · -- n <= 45444098093
            exact RamareSaouter2003.prime_interval_nat_ladder_c00651 n (by omega) (by omega)
