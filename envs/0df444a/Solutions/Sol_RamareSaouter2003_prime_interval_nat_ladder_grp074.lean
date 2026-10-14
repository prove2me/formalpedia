-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T06:16:39.551096+00:00
-- url     : https://prove2.me/submissions/aa7ce803-7438-4ffd-b56f-901b5c67b17d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03700

theorem solution (n : Nat)
    (hn : 75655853035559 < n) (hupper : n <= 85608001936621) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 80478235648859 n with h2 | h2
  · -- n > 80478235648859
    rcases Nat.lt_or_ge 82900983998671 n with h4 | h4
    · -- n > 82900983998671
      rcases Nat.lt_or_ge 84139573232887 n with h6 | h6
      · -- n > 84139573232887
        rcases Nat.lt_or_ge 84765790133923 n with h8 | h8
        · -- n > 84765790133923
          rcases Nat.lt_or_ge 85185855198679 n with h10 | h10
          · -- n > 85185855198679
            rcases Nat.lt_or_ge 85396667714989 n with h12 | h12
            · -- n > 85396667714989
              exact RamareSaouter2003.prime_interval_nat_ladder_c03700 n (by omega) (by omega)
            · -- n <= 85396667714989
              exact RamareSaouter2003.prime_interval_nat_ladder_c03699 n (by omega) (by omega)
          · -- n <= 85185855198679
            rcases Nat.lt_or_ge 84975563099953 n with h12 | h12
            · -- n > 84975563099953
              exact RamareSaouter2003.prime_interval_nat_ladder_c03698 n (by omega) (by omega)
            · -- n <= 84975563099953
              exact RamareSaouter2003.prime_interval_nat_ladder_c03697 n (by omega) (by omega)
        · -- n <= 84765790133923
          rcases Nat.lt_or_ge 84347796477101 n with h10 | h10
          · -- n > 84347796477101
            rcases Nat.lt_or_ge 84556535019107 n with h12 | h12
            · -- n > 84556535019107
              exact RamareSaouter2003.prime_interval_nat_ladder_c03696 n (by omega) (by omega)
            · -- n <= 84556535019107
              exact RamareSaouter2003.prime_interval_nat_ladder_c03695 n (by omega) (by omega)
          · -- n <= 84347796477101
            exact RamareSaouter2003.prime_interval_nat_ladder_c03694 n (by omega) (by omega)
      · -- n <= 84139573232887
        rcases Nat.lt_or_ge 83517982580017 n with h8 | h8
        · -- n > 83517982580017
          rcases Nat.lt_or_ge 83724667551641 n with h10 | h10
          · -- n > 83724667551641
            rcases Nat.lt_or_ge 83931864014039 n with h12 | h12
            · -- n > 83931864014039
              exact RamareSaouter2003.prime_interval_nat_ladder_c03693 n (by omega) (by omega)
            · -- n <= 83931864014039
              exact RamareSaouter2003.prime_interval_nat_ladder_c03692 n (by omega) (by omega)
          · -- n <= 83724667551641
            exact RamareSaouter2003.prime_interval_nat_ladder_c03691 n (by omega) (by omega)
        · -- n <= 83517982580017
          rcases Nat.lt_or_ge 83106142061599 n with h10 | h10
          · -- n > 83106142061599
            rcases Nat.lt_or_ge 83311807836529 n with h12 | h12
            · -- n > 83311807836529
              exact RamareSaouter2003.prime_interval_nat_ladder_c03690 n (by omega) (by omega)
            · -- n <= 83311807836529
              exact RamareSaouter2003.prime_interval_nat_ladder_c03689 n (by omega) (by omega)
          · -- n <= 83106142061599
            exact RamareSaouter2003.prime_interval_nat_ladder_c03688 n (by omega) (by omega)
    · -- n <= 82900983998671
      rcases Nat.lt_or_ge 81680627603863 n with h6 | h6
      · -- n > 81680627603863
        rcases Nat.lt_or_ge 82288543564879 n with h8 | h8
        · -- n > 82288543564879
          rcases Nat.lt_or_ge 82492185999217 n with h10 | h10
          · -- n > 82492185999217
            rcases Nat.lt_or_ge 82696332394769 n with h12 | h12
            · -- n > 82696332394769
              exact RamareSaouter2003.prime_interval_nat_ladder_c03687 n (by omega) (by omega)
            · -- n <= 82696332394769
              exact RamareSaouter2003.prime_interval_nat_ladder_c03686 n (by omega) (by omega)
          · -- n <= 82492185999217
            exact RamareSaouter2003.prime_interval_nat_ladder_c03685 n (by omega) (by omega)
        · -- n <= 82288543564879
          rcases Nat.lt_or_ge 81882765606623 n with h10 | h10
          · -- n > 81882765606623
            rcases Nat.lt_or_ge 82085403847651 n with h12 | h12
            · -- n > 82085403847651
              exact RamareSaouter2003.prime_interval_nat_ladder_c03684 n (by omega) (by omega)
            · -- n <= 82085403847651
              exact RamareSaouter2003.prime_interval_nat_ladder_c03683 n (by omega) (by omega)
          · -- n <= 81882765606623
            exact RamareSaouter2003.prime_interval_nat_ladder_c03682 n (by omega) (by omega)
      · -- n <= 81680627603863
        rcases Nat.lt_or_ge 81077202691283 n with h8 | h8
        · -- n > 81077202691283
          rcases Nat.lt_or_ge 81277847376541 n with h10 | h10
          · -- n > 81277847376541
            rcases Nat.lt_or_ge 81478988604469 n with h12 | h12
            · -- n > 81478988604469
              exact RamareSaouter2003.prime_interval_nat_ladder_c03681 n (by omega) (by omega)
            · -- n <= 81478988604469
              exact RamareSaouter2003.prime_interval_nat_ladder_c03680 n (by omega) (by omega)
          · -- n <= 81277847376541
            exact RamareSaouter2003.prime_interval_nat_ladder_c03679 n (by omega) (by omega)
        · -- n <= 81077202691283
          rcases Nat.lt_or_ge 80677398048823 n with h10 | h10
          · -- n > 80677398048823
            rcases Nat.lt_or_ge 80877053323049 n with h12 | h12
            · -- n > 80877053323049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03678 n (by omega) (by omega)
            · -- n <= 80877053323049
              exact RamareSaouter2003.prime_interval_nat_ladder_c03677 n (by omega) (by omega)
          · -- n <= 80677398048823
            exact RamareSaouter2003.prime_interval_nat_ladder_c03676 n (by omega) (by omega)
  · -- n <= 80478235648859
    rcases Nat.lt_or_ge 77933426489047 n with h4 | h4
    · -- n > 77933426489047
      rcases Nat.lt_or_ge 79097797505599 n with h6 | h6
      · -- n > 79097797505599
        rcases Nat.lt_or_ge 79686490503931 n with h8 | h8
        · -- n > 79686490503931
          rcases Nat.lt_or_ge 80081384608417 n with h10 | h10
          · -- n > 80081384608417
            rcases Nat.lt_or_ge 80279564906591 n with h12 | h12
            · -- n > 80279564906591
              exact RamareSaouter2003.prime_interval_nat_ladder_c03675 n (by omega) (by omega)
            · -- n <= 80279564906591
              exact RamareSaouter2003.prime_interval_nat_ladder_c03674 n (by omega) (by omega)
          · -- n <= 80081384608417
            rcases Nat.lt_or_ge 79883693543299 n with h12 | h12
            · -- n > 79883693543299
              exact RamareSaouter2003.prime_interval_nat_ladder_c03673 n (by omega) (by omega)
            · -- n <= 79883693543299
              exact RamareSaouter2003.prime_interval_nat_ladder_c03672 n (by omega) (by omega)
        · -- n <= 79686490503931
          rcases Nat.lt_or_ge 79293543685231 n with h10 | h10
          · -- n > 79293543685231
            rcases Nat.lt_or_ge 79489774285121 n with h12 | h12
            · -- n > 79489774285121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03671 n (by omega) (by omega)
            · -- n <= 79489774285121
              exact RamareSaouter2003.prime_interval_nat_ladder_c03670 n (by omega) (by omega)
          · -- n <= 79293543685231
            exact RamareSaouter2003.prime_interval_nat_ladder_c03669 n (by omega) (by omega)
      · -- n <= 79097797505599
        rcases Nat.lt_or_ge 78513453543589 n with h8 | h8
        · -- n > 78513453543589
          rcases Nat.lt_or_ge 78707753626153 n with h10 | h10
          · -- n > 78707753626153
            rcases Nat.lt_or_ge 78902534550149 n with h12 | h12
            · -- n > 78902534550149
              exact RamareSaouter2003.prime_interval_nat_ladder_c03668 n (by omega) (by omega)
            · -- n <= 78902534550149
              exact RamareSaouter2003.prime_interval_nat_ladder_c03667 n (by omega) (by omega)
          · -- n <= 78707753626153
            exact RamareSaouter2003.prime_interval_nat_ladder_c03666 n (by omega) (by omega)
        · -- n <= 78513453543589
          rcases Nat.lt_or_ge 78126291157553 n with h10 | h10
          · -- n > 78126291157553
            rcases Nat.lt_or_ge 78319633115371 n with h12 | h12
            · -- n > 78319633115371
              exact RamareSaouter2003.prime_interval_nat_ladder_c03665 n (by omega) (by omega)
            · -- n <= 78319633115371
              exact RamareSaouter2003.prime_interval_nat_ladder_c03664 n (by omega) (by omega)
          · -- n <= 78126291157553
            exact RamareSaouter2003.prime_interval_nat_ladder_c03663 n (by omega) (by omega)
    · -- n <= 77933426489047
      rcases Nat.lt_or_ge 76786195771387 n with h6 | h6
      · -- n > 76786195771387
        rcases Nat.lt_or_ge 77357684450549 n with h8 | h8
        · -- n > 77357684450549
          rcases Nat.lt_or_ge 77549124309593 n with h10 | h10
          · -- n > 77549124309593
            rcases Nat.lt_or_ge 77741037931657 n with h12 | h12
            · -- n > 77741037931657
              exact RamareSaouter2003.prime_interval_nat_ladder_c03662 n (by omega) (by omega)
            · -- n <= 77741037931657
              exact RamareSaouter2003.prime_interval_nat_ladder_c03661 n (by omega) (by omega)
          · -- n <= 77549124309593
            exact RamareSaouter2003.prime_interval_nat_ladder_c03660 n (by omega) (by omega)
        · -- n <= 77357684450549
          rcases Nat.lt_or_ge 76976221346611 n with h10 | h10
          · -- n > 76976221346611
            rcases Nat.lt_or_ge 77166717185071 n with h12 | h12
            · -- n > 77166717185071
              exact RamareSaouter2003.prime_interval_nat_ladder_c03659 n (by omega) (by omega)
            · -- n <= 77166717185071
              exact RamareSaouter2003.prime_interval_nat_ladder_c03658 n (by omega) (by omega)
          · -- n <= 76976221346611
            exact RamareSaouter2003.prime_interval_nat_ladder_c03657 n (by omega) (by omega)
      · -- n <= 76786195771387
        rcases Nat.lt_or_ge 76218929029657 n with h8 | h8
        · -- n > 76218929029657
          rcases Nat.lt_or_ge 76407550769513 n with h10 | h10
          · -- n > 76407550769513
            rcases Nat.lt_or_ge 76596639298301 n with h12 | h12
            · -- n > 76596639298301
              exact RamareSaouter2003.prime_interval_nat_ladder_c03656 n (by omega) (by omega)
            · -- n <= 76596639298301
              exact RamareSaouter2003.prime_interval_nat_ladder_c03655 n (by omega) (by omega)
          · -- n <= 76407550769513
            exact RamareSaouter2003.prime_interval_nat_ladder_c03654 n (by omega) (by omega)
        · -- n <= 76218929029657
          rcases Nat.lt_or_ge 75843081310757 n with h10 | h10
          · -- n > 75843081310757
            rcases Nat.lt_or_ge 76030772926543 n with h12 | h12
            · -- n > 76030772926543
              exact RamareSaouter2003.prime_interval_nat_ladder_c03653 n (by omega) (by omega)
            · -- n <= 76030772926543
              exact RamareSaouter2003.prime_interval_nat_ladder_c03652 n (by omega) (by omega)
          · -- n <= 75843081310757
            exact RamareSaouter2003.prime_interval_nat_ladder_c03651 n (by omega) (by omega)
