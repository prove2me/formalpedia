-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T22:48:12.340889+00:00
-- url     : https://prove2.me/submissions/4e2050b7-cc58-4f58-a438-e26a52aff5be

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00750

theorem solution (n : Nat)
    (hn : 50809618939 < n) (hupper : n <= 56954749447) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 53792528759 n with h2 | h2
  · -- n > 53792528759
    rcases Nat.lt_or_ge 55287353581 n with h4 | h4
    · -- n > 55287353581
      rcases Nat.lt_or_ge 56050628423 n with h6 | h6
      · -- n > 56050628423
        rcases Nat.lt_or_ge 56436298153 n with h8 | h8
        · -- n > 56436298153
          rcases Nat.lt_or_ge 56694917759 n with h10 | h10
          · -- n > 56694917759
            rcases Nat.lt_or_ge 56824681783 n with h12 | h12
            · -- n > 56824681783
              exact RamareSaouter2003.prime_interval_nat_ladder_c00750 n (by omega) (by omega)
            · -- n <= 56824681783
              exact RamareSaouter2003.prime_interval_nat_ladder_c00749 n (by omega) (by omega)
          · -- n <= 56694917759
            rcases Nat.lt_or_ge 56565456763 n with h12 | h12
            · -- n > 56565456763
              exact RamareSaouter2003.prime_interval_nat_ladder_c00748 n (by omega) (by omega)
            · -- n <= 56565456763
              exact RamareSaouter2003.prime_interval_nat_ladder_c00747 n (by omega) (by omega)
        · -- n <= 56436298153
          rcases Nat.lt_or_ge 56178884677 n with h10 | h10
          · -- n > 56178884677
            rcases Nat.lt_or_ge 56307440999 n with h12 | h12
            · -- n > 56307440999
              exact RamareSaouter2003.prime_interval_nat_ladder_c00746 n (by omega) (by omega)
            · -- n <= 56307440999
              exact RamareSaouter2003.prime_interval_nat_ladder_c00745 n (by omega) (by omega)
          · -- n <= 56178884677
            exact RamareSaouter2003.prime_interval_nat_ladder_c00744 n (by omega) (by omega)
      · -- n <= 56050628423
        rcases Nat.lt_or_ge 55667653357 n with h8 | h8
        · -- n > 55667653357
          rcases Nat.lt_or_ge 55795013429 n with h10 | h10
          · -- n > 55795013429
            rcases Nat.lt_or_ge 55922671583 n with h12 | h12
            · -- n > 55922671583
              exact RamareSaouter2003.prime_interval_nat_ladder_c00743 n (by omega) (by omega)
            · -- n <= 55922671583
              exact RamareSaouter2003.prime_interval_nat_ladder_c00742 n (by omega) (by omega)
          · -- n <= 55795013429
            exact RamareSaouter2003.prime_interval_nat_ladder_c00741 n (by omega) (by omega)
        · -- n <= 55667653357
          rcases Nat.lt_or_ge 55413824111 n with h10 | h10
          · -- n > 55413824111
            rcases Nat.lt_or_ge 55540590461 n with h12 | h12
            · -- n > 55540590461
              exact RamareSaouter2003.prime_interval_nat_ladder_c00740 n (by omega) (by omega)
            · -- n <= 55540590461
              exact RamareSaouter2003.prime_interval_nat_ladder_c00739 n (by omega) (by omega)
          · -- n <= 55413824111
            exact RamareSaouter2003.prime_interval_nat_ladder_c00738 n (by omega) (by omega)
    · -- n <= 55287353581
      rcases Nat.lt_or_ge 54534703961 n with h6 | h6
      · -- n > 54534703961
        rcases Nat.lt_or_ge 54909710147 n with h8 | h8
        · -- n > 54909710147
          rcases Nat.lt_or_ge 55035297269 n with h10 | h10
          · -- n > 55035297269
            rcases Nat.lt_or_ge 55161178217 n with h12 | h12
            · -- n > 55161178217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00737 n (by omega) (by omega)
            · -- n <= 55161178217
              exact RamareSaouter2003.prime_interval_nat_ladder_c00736 n (by omega) (by omega)
          · -- n <= 55035297269
            exact RamareSaouter2003.prime_interval_nat_ladder_c00735 n (by omega) (by omega)
        · -- n <= 54909710147
          rcases Nat.lt_or_ge 54659414137 n with h10 | h10
          · -- n > 54659414137
            rcases Nat.lt_or_ge 54784415977 n with h12 | h12
            · -- n > 54784415977
              exact RamareSaouter2003.prime_interval_nat_ladder_c00734 n (by omega) (by omega)
            · -- n <= 54784415977
              exact RamareSaouter2003.prime_interval_nat_ladder_c00733 n (by omega) (by omega)
          · -- n <= 54659414137
            exact RamareSaouter2003.prime_interval_nat_ladder_c00732 n (by omega) (by omega)
      · -- n <= 54534703961
        rcases Nat.lt_or_ge 54162316519 n with h8 | h8
        · -- n > 54162316519
          rcases Nat.lt_or_ge 54286155953 n with h10 | h10
          · -- n > 54286155953
            rcases Nat.lt_or_ge 54410284739 n with h12 | h12
            · -- n > 54410284739
              exact RamareSaouter2003.prime_interval_nat_ladder_c00731 n (by omega) (by omega)
            · -- n <= 54410284739
              exact RamareSaouter2003.prime_interval_nat_ladder_c00730 n (by omega) (by omega)
          · -- n <= 54286155953
            exact RamareSaouter2003.prime_interval_nat_ladder_c00729 n (by omega) (by omega)
        · -- n <= 54162316519
          rcases Nat.lt_or_ge 53915503571 n with h10 | h10
          · -- n > 53915503571
            rcases Nat.lt_or_ge 54038765953 n with h12 | h12
            · -- n > 54038765953
              exact RamareSaouter2003.prime_interval_nat_ladder_c00728 n (by omega) (by omega)
            · -- n <= 54038765953
              exact RamareSaouter2003.prime_interval_nat_ladder_c00727 n (by omega) (by omega)
          · -- n <= 53915503571
            exact RamareSaouter2003.prime_interval_nat_ladder_c00726 n (by omega) (by omega)
  · -- n <= 53792528759
    rcases Nat.lt_or_ge 52219708417 n with h4 | h4
    · -- n > 52219708417
      rcases Nat.lt_or_ge 52939697407 n with h6 | h6
      · -- n > 52939697407
        rcases Nat.lt_or_ge 53303490703 n with h8 | h8
        · -- n > 53303490703
          rcases Nat.lt_or_ge 53547438871 n with h10 | h10
          · -- n > 53547438871
            rcases Nat.lt_or_ge 53669840773 n with h12 | h12
            · -- n > 53669840773
              exact RamareSaouter2003.prime_interval_nat_ladder_c00725 n (by omega) (by omega)
            · -- n <= 53669840773
              exact RamareSaouter2003.prime_interval_nat_ladder_c00724 n (by omega) (by omega)
          · -- n <= 53547438871
            rcases Nat.lt_or_ge 53425322417 n with h12 | h12
            · -- n > 53425322417
              exact RamareSaouter2003.prime_interval_nat_ladder_c00723 n (by omega) (by omega)
            · -- n <= 53425322417
              exact RamareSaouter2003.prime_interval_nat_ladder_c00722 n (by omega) (by omega)
        · -- n <= 53303490703
          rcases Nat.lt_or_ge 53060678903 n with h10 | h10
          · -- n > 53060678903
            rcases Nat.lt_or_ge 53181943109 n with h12 | h12
            · -- n > 53181943109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00721 n (by omega) (by omega)
            · -- n <= 53181943109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00720 n (by omega) (by omega)
          · -- n <= 53060678903
            exact RamareSaouter2003.prime_interval_nat_ladder_c00719 n (by omega) (by omega)
      · -- n <= 52939697407
        rcases Nat.lt_or_ge 52578442733 n with h8 | h8
        · -- n > 52578442733
          rcases Nat.lt_or_ge 52698579943 n with h10 | h10
          · -- n > 52698579943
            rcases Nat.lt_or_ge 52818997991 n with h12 | h12
            · -- n > 52818997991
              exact RamareSaouter2003.prime_interval_nat_ladder_c00718 n (by omega) (by omega)
            · -- n <= 52818997991
              exact RamareSaouter2003.prime_interval_nat_ladder_c00717 n (by omega) (by omega)
          · -- n <= 52698579943
            exact RamareSaouter2003.prime_interval_nat_ladder_c00716 n (by omega) (by omega)
        · -- n <= 52578442733
          rcases Nat.lt_or_ge 52339007569 n with h10 | h10
          · -- n > 52339007569
            rcases Nat.lt_or_ge 52458585457 n with h12 | h12
            · -- n > 52458585457
              exact RamareSaouter2003.prime_interval_nat_ladder_c00715 n (by omega) (by omega)
            · -- n <= 52458585457
              exact RamareSaouter2003.prime_interval_nat_ladder_c00714 n (by omega) (by omega)
          · -- n <= 52339007569
            exact RamareSaouter2003.prime_interval_nat_ladder_c00713 n (by omega) (by omega)
    · -- n <= 52219708417
      rcases Nat.lt_or_ge 51509729569 n with h6 | h6
      · -- n > 51509729569
        rcases Nat.lt_or_ge 51863476633 n with h8 | h8
        · -- n > 51863476633
          rcases Nat.lt_or_ge 51981943597 n with h10 | h10
          · -- n > 51981943597
            rcases Nat.lt_or_ge 52100687297 n with h12 | h12
            · -- n > 52100687297
              exact RamareSaouter2003.prime_interval_nat_ladder_c00712 n (by omega) (by omega)
            · -- n <= 52100687297
              exact RamareSaouter2003.prime_interval_nat_ladder_c00711 n (by omega) (by omega)
          · -- n <= 51981943597
            exact RamareSaouter2003.prime_interval_nat_ladder_c00710 n (by omega) (by omega)
        · -- n <= 51863476633
          rcases Nat.lt_or_ge 51627370283 n with h10 | h10
          · -- n > 51627370283
            rcases Nat.lt_or_ge 51745285747 n with h12 | h12
            · -- n > 51745285747
              exact RamareSaouter2003.prime_interval_nat_ladder_c00709 n (by omega) (by omega)
            · -- n <= 51745285747
              exact RamareSaouter2003.prime_interval_nat_ladder_c00708 n (by omega) (by omega)
          · -- n <= 51627370283
            exact RamareSaouter2003.prime_interval_nat_ladder_c00707 n (by omega) (by omega)
      · -- n <= 51509729569
        rcases Nat.lt_or_ge 51158449541 n with h8 | h8
        · -- n > 51158449541
          rcases Nat.lt_or_ge 51275269897 n with h10 | h10
          · -- n > 51275269897
            rcases Nat.lt_or_ge 51392362981 n with h12 | h12
            · -- n > 51392362981
              exact RamareSaouter2003.prime_interval_nat_ladder_c00706 n (by omega) (by omega)
            · -- n <= 51392362981
              exact RamareSaouter2003.prime_interval_nat_ladder_c00705 n (by omega) (by omega)
          · -- n <= 51275269897
            exact RamareSaouter2003.prime_interval_nat_ladder_c00704 n (by omega) (by omega)
        · -- n <= 51158449541
          rcases Nat.lt_or_ge 50925624713 n with h10 | h10
          · -- n > 50925624713
            rcases Nat.lt_or_ge 51041901353 n with h12 | h12
            · -- n > 51041901353
              exact RamareSaouter2003.prime_interval_nat_ladder_c00703 n (by omega) (by omega)
            · -- n <= 51041901353
              exact RamareSaouter2003.prime_interval_nat_ladder_c00702 n (by omega) (by omega)
          · -- n <= 50925624713
            exact RamareSaouter2003.prime_interval_nat_ladder_c00701 n (by omega) (by omega)
