-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T11:25:25.14492+00:00
-- url     : https://prove2.me/submissions/c7c6e7c0-cb48-44ee-b5f4-6e8caaee3854

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01800

theorem solution (n : Nat)
    (hn : 665289962371 < n) (hupper : n <= 755098777861) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 708760284059 n with h2 | h2
  · -- n > 708760284059
    rcases Nat.lt_or_ge 730633340659 n with h4 | h4
    · -- n > 730633340659
      rcases Nat.lt_or_ge 741824076589 n with h6 | h6
      · -- n > 741824076589
        rcases Nat.lt_or_ge 747484152277 n with h8 | h8
        · -- n > 747484152277
          rcases Nat.lt_or_ge 751281729403 n with h10 | h10
          · -- n > 751281729403
            rcases Nat.lt_or_ge 753187813307 n with h12 | h12
            · -- n > 753187813307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01800 n (by omega) (by omega)
            · -- n <= 753187813307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01799 n (by omega) (by omega)
          · -- n <= 751281729403
            rcases Nat.lt_or_ge 749380513187 n with h12 | h12
            · -- n > 749380513187
              exact RamareSaouter2003.prime_interval_nat_ladder_c01798 n (by omega) (by omega)
            · -- n <= 749380513187
              exact RamareSaouter2003.prime_interval_nat_ladder_c01797 n (by omega) (by omega)
        · -- n <= 747484152277
          rcases Nat.lt_or_ge 743705946433 n with h10 | h10
          · -- n > 743705946433
            rcases Nat.lt_or_ge 745592634179 n with h12 | h12
            · -- n > 745592634179
              exact RamareSaouter2003.prime_interval_nat_ladder_c01796 n (by omega) (by omega)
            · -- n <= 745592634179
              exact RamareSaouter2003.prime_interval_nat_ladder_c01795 n (by omega) (by omega)
          · -- n <= 743705946433
            exact RamareSaouter2003.prime_interval_nat_ladder_c01794 n (by omega) (by omega)
      · -- n <= 741824076589
        rcases Nat.lt_or_ge 736207250561 n with h8 | h8
        · -- n > 736207250561
          rcases Nat.lt_or_ge 738074741069 n with h10 | h10
          · -- n > 738074741069
            rcases Nat.lt_or_ge 739947012247 n with h12 | h12
            · -- n > 739947012247
              exact RamareSaouter2003.prime_interval_nat_ladder_c01793 n (by omega) (by omega)
            · -- n <= 739947012247
              exact RamareSaouter2003.prime_interval_nat_ladder_c01792 n (by omega) (by omega)
          · -- n <= 738074741069
            exact RamareSaouter2003.prime_interval_nat_ladder_c01791 n (by omega) (by omega)
        · -- n <= 736207250561
          rcases Nat.lt_or_ge 732486562673 n with h10 | h10
          · -- n > 732486562673
            rcases Nat.lt_or_ge 734344528531 n with h12 | h12
            · -- n > 734344528531
              exact RamareSaouter2003.prime_interval_nat_ladder_c01790 n (by omega) (by omega)
            · -- n <= 734344528531
              exact RamareSaouter2003.prime_interval_nat_ladder_c01789 n (by omega) (by omega)
          · -- n <= 732486562673
            exact RamareSaouter2003.prime_interval_nat_ladder_c01788 n (by omega) (by omega)
    · -- n <= 730633340659
      rcases Nat.lt_or_ge 719612948381 n with h6 | h6
      · -- n > 719612948381
        rcases Nat.lt_or_ge 725102016013 n with h8 | h8
        · -- n > 725102016013
          rcases Nat.lt_or_ge 726941079503 n with h10 | h10
          · -- n > 726941079503
            rcases Nat.lt_or_ge 728784850333 n with h12 | h12
            · -- n > 728784850333
              exact RamareSaouter2003.prime_interval_nat_ladder_c01787 n (by omega) (by omega)
            · -- n <= 728784850333
              exact RamareSaouter2003.prime_interval_nat_ladder_c01786 n (by omega) (by omega)
          · -- n <= 726941079503
            exact RamareSaouter2003.prime_interval_nat_ladder_c01785 n (by omega) (by omega)
        · -- n <= 725102016013
          rcases Nat.lt_or_ge 721437962549 n with h10 | h10
          · -- n > 721437962549
            rcases Nat.lt_or_ge 723267647737 n with h12 | h12
            · -- n > 723267647737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01784 n (by omega) (by omega)
            · -- n <= 723267647737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01783 n (by omega) (by omega)
          · -- n <= 721437962549
            exact RamareSaouter2003.prime_interval_nat_ladder_c01782 n (by omega) (by omega)
      · -- n <= 719612948381
        rcases Nat.lt_or_ge 714165812221 n with h8 | h8
        · -- n > 714165812221
          rcases Nat.lt_or_ge 715976885251 n with h10 | h10
          · -- n > 715976885251
            rcases Nat.lt_or_ge 717792593369 n with h12 | h12
            · -- n > 717792593369
              exact RamareSaouter2003.prime_interval_nat_ladder_c01781 n (by omega) (by omega)
            · -- n <= 717792593369
              exact RamareSaouter2003.prime_interval_nat_ladder_c01780 n (by omega) (by omega)
          · -- n <= 715976885251
            exact RamareSaouter2003.prime_interval_nat_ladder_c01779 n (by omega) (by omega)
        · -- n <= 714165812221
          rcases Nat.lt_or_ge 710557523537 n with h10 | h10
          · -- n > 710557523537
            rcases Nat.lt_or_ge 712359362251 n with h12 | h12
            · -- n > 712359362251
              exact RamareSaouter2003.prime_interval_nat_ladder_c01778 n (by omega) (by omega)
            · -- n <= 712359362251
              exact RamareSaouter2003.prime_interval_nat_ladder_c01777 n (by omega) (by omega)
          · -- n <= 710557523537
            exact RamareSaouter2003.prime_interval_nat_ladder_c01776 n (by omega) (by omega)
  · -- n <= 708760284059
    rcases Nat.lt_or_ge 685809361249 n with h4 | h4
    · -- n > 685809361249
      rcases Nat.lt_or_ge 696307397623 n with h6 | h6
      · -- n > 696307397623
        rcases Nat.lt_or_ge 701617082951 n with h8 | h8
        · -- n > 701617082951
          rcases Nat.lt_or_ge 705179555741 n with h10 | h10
          · -- n > 705179555741
            rcases Nat.lt_or_ge 706967632073 n with h12 | h12
            · -- n > 706967632073
              exact RamareSaouter2003.prime_interval_nat_ladder_c01775 n (by omega) (by omega)
            · -- n <= 706967632073
              exact RamareSaouter2003.prime_interval_nat_ladder_c01774 n (by omega) (by omega)
          · -- n <= 705179555741
            rcases Nat.lt_or_ge 703396043291 n with h12 | h12
            · -- n > 703396043291
              exact RamareSaouter2003.prime_interval_nat_ladder_c01773 n (by omega) (by omega)
            · -- n <= 703396043291
              exact RamareSaouter2003.prime_interval_nat_ladder_c01772 n (by omega) (by omega)
        · -- n <= 701617082951
          rcases Nat.lt_or_ge 698072771813 n with h10 | h10
          · -- n > 698072771813
            rcases Nat.lt_or_ge 699842663029 n with h12 | h12
            · -- n > 699842663029
              exact RamareSaouter2003.prime_interval_nat_ladder_c01771 n (by omega) (by omega)
            · -- n <= 699842663029
              exact RamareSaouter2003.prime_interval_nat_ladder_c01770 n (by omega) (by omega)
          · -- n <= 698072771813
            exact RamareSaouter2003.prime_interval_nat_ladder_c01769 n (by omega) (by omega)
      · -- n <= 696307397623
        rcases Nat.lt_or_ge 691038261209 n with h8 | h8
        · -- n > 691038261209
          rcases Nat.lt_or_ge 692790153919 n with h10 | h10
          · -- n > 692790153919
            rcases Nat.lt_or_ge 694546528861 n with h12 | h12
            · -- n > 694546528861
              exact RamareSaouter2003.prime_interval_nat_ladder_c01768 n (by omega) (by omega)
            · -- n <= 694546528861
              exact RamareSaouter2003.prime_interval_nat_ladder_c01767 n (by omega) (by omega)
          · -- n <= 692790153919
            exact RamareSaouter2003.prime_interval_nat_ladder_c01766 n (by omega) (by omega)
        · -- n <= 691038261209
          rcases Nat.lt_or_ge 687547876381 n with h10 | h10
          · -- n > 687547876381
            rcases Nat.lt_or_ge 689290839173 n with h12 | h12
            · -- n > 689290839173
              exact RamareSaouter2003.prime_interval_nat_ladder_c01765 n (by omega) (by omega)
            · -- n <= 689290839173
              exact RamareSaouter2003.prime_interval_nat_ladder_c01764 n (by omega) (by omega)
          · -- n <= 687547876381
            exact RamareSaouter2003.prime_interval_nat_ladder_c01763 n (by omega) (by omega)
    · -- n <= 685809361249
      rcases Nat.lt_or_ge 675471033407 n with h6 | h6
      · -- n > 675471033407
        rcases Nat.lt_or_ge 680620388083 n with h8 | h8
        · -- n > 680620388083
          rcases Nat.lt_or_ge 682345628593 n with h10 | h10
          · -- n > 682345628593
            rcases Nat.lt_or_ge 684075282463 n with h12 | h12
            · -- n > 684075282463
              exact RamareSaouter2003.prime_interval_nat_ladder_c01762 n (by omega) (by omega)
            · -- n <= 684075282463
              exact RamareSaouter2003.prime_interval_nat_ladder_c01761 n (by omega) (by omega)
          · -- n <= 682345628593
            exact RamareSaouter2003.prime_interval_nat_ladder_c01760 n (by omega) (by omega)
        · -- n <= 680620388083
          rcases Nat.lt_or_ge 677183101783 n with h10 | h10
          · -- n > 677183101783
            rcases Nat.lt_or_ge 678899549567 n with h12 | h12
            · -- n > 678899549567
              exact RamareSaouter2003.prime_interval_nat_ladder_c01759 n (by omega) (by omega)
            · -- n <= 678899549567
              exact RamareSaouter2003.prime_interval_nat_ladder_c01758 n (by omega) (by omega)
          · -- n <= 677183101783
            exact RamareSaouter2003.prime_interval_nat_ladder_c01757 n (by omega) (by omega)
      · -- n <= 675471033407
        rcases Nat.lt_or_ge 670360992589 n with h8 | h8
        · -- n > 670360992589
          rcases Nat.lt_or_ge 672059990143 n with h10 | h10
          · -- n > 672059990143
            rcases Nat.lt_or_ge 673763333351 n with h12 | h12
            · -- n > 673763333351
              exact RamareSaouter2003.prime_interval_nat_ladder_c01756 n (by omega) (by omega)
            · -- n <= 673763333351
              exact RamareSaouter2003.prime_interval_nat_ladder_c01755 n (by omega) (by omega)
          · -- n <= 672059990143
            exact RamareSaouter2003.prime_interval_nat_ladder_c01754 n (by omega) (by omega)
        · -- n <= 670360992589
          rcases Nat.lt_or_ge 666975989851 n with h10 | h10
          · -- n > 666975989851
            rcases Nat.lt_or_ge 668666329537 n with h12 | h12
            · -- n > 668666329537
              exact RamareSaouter2003.prime_interval_nat_ladder_c01753 n (by omega) (by omega)
            · -- n <= 668666329537
              exact RamareSaouter2003.prime_interval_nat_ladder_c01752 n (by omega) (by omega)
          · -- n <= 666975989851
            exact RamareSaouter2003.prime_interval_nat_ladder_c01751 n (by omega) (by omega)
