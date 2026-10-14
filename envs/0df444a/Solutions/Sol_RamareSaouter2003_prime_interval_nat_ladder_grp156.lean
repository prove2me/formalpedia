-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T09:40:04.833702+00:00
-- url     : https://prove2.me/submissions/26600dd0-e19e-4322-bee4-5c63410bfa6c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07750
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07786

theorem solution (n : Nat)
    (hn : 7138238304410545217 < n) (hupper : n <= 8198927391296255473) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 7639414894591921261 n with h2 | h2
  · -- n > 7639414894591921261
    rcases Nat.lt_or_ge 7903047985073758579 n with h4 | h4
    · -- n > 7903047985073758579
      rcases Nat.lt_or_ge 8038257094650947309 n with h6 | h6
      · -- n > 8038257094650947309
        rcases Nat.lt_or_ge 8106726268993120931 n with h8 | h8
        · -- n > 8106726268993120931
          rcases Nat.lt_or_ge 8152696499335122473 n with h10 | h10
          · -- n > 8152696499335122473
            rcases Nat.lt_or_ge 8175779282626402957 n with h12 | h12
            · -- n > 8175779282626402957
              exact RamareSaouter2003.prime_interval_nat_ladder_c07786 n (by omega) (by omega)
            · -- n <= 8175779282626402957
              exact RamareSaouter2003.prime_interval_nat_ladder_c07785 n (by omega) (by omega)
          · -- n <= 8152696499335122473
            rcases Nat.lt_or_ge 8129678902405131419 n with h12 | h12
            · -- n > 8129678902405131419
              exact RamareSaouter2003.prime_interval_nat_ladder_c07784 n (by omega) (by omega)
            · -- n <= 8129678902405131419
              exact RamareSaouter2003.prime_interval_nat_ladder_c07783 n (by omega) (by omega)
        · -- n <= 8106726268993120931
          rcases Nat.lt_or_ge 8061015408578786561 n with h10 | h10
          · -- n > 8061015408578786561
            rcases Nat.lt_or_ge 8083838466258539059 n with h12 | h12
            · -- n > 8083838466258539059
              exact RamareSaouter2003.prime_interval_nat_ladder_c07782 n (by omega) (by omega)
            · -- n <= 8083838466258539059
              exact RamareSaouter2003.prime_interval_nat_ladder_c07781 n (by omega) (by omega)
          · -- n <= 8061015408578786561
            exact RamareSaouter2003.prime_interval_nat_ladder_c07780 n (by omega) (by omega)
      · -- n <= 8038257094650947309
        rcases Nat.lt_or_ge 7970365830950305873 n with h8 | h8
        · -- n > 7970365830950305873
          rcases Nat.lt_or_ge 7992932353267025323 n with h10 | h10
          · -- n > 7992932353267025323
            rcases Nat.lt_or_ge 8015562700914146239 n with h12 | h12
            · -- n > 8015562700914146239
              exact RamareSaouter2003.prime_interval_nat_ladder_c07779 n (by omega) (by omega)
            · -- n <= 8015562700914146239
              exact RamareSaouter2003.prime_interval_nat_ladder_c07778 n (by omega) (by omega)
          · -- n <= 7992932353267025323
            exact RamareSaouter2003.prime_interval_nat_ladder_c07777 n (by omega) (by omega)
        · -- n <= 7970365830950305873
          rcases Nat.lt_or_ge 7925423851677105253 n with h10 | h10
          · -- n > 7925423851677105253
            rcases Nat.lt_or_ge 7947863049779226527 n with h12 | h12
            · -- n > 7947863049779226527
              exact RamareSaouter2003.prime_interval_nat_ladder_c07776 n (by omega) (by omega)
            · -- n <= 7947863049779226527
              exact RamareSaouter2003.prime_interval_nat_ladder_c07775 n (by omega) (by omega)
          · -- n <= 7925423851677105253
            exact RamareSaouter2003.prime_interval_nat_ladder_c07774 n (by omega) (by omega)
    · -- n <= 7903047985073758579
      rcases Nat.lt_or_ge 7770113224424102369 n with h6 | h6
      · -- n > 7770113224424102369
        rcases Nat.lt_or_ge 7836298679467036721 n with h8 | h8
        · -- n > 7836298679467036721
          rcases Nat.lt_or_ge 7858485554889704341 n with h10 | h10
          · -- n > 7858485554889704341
            rcases Nat.lt_or_ge 7880735252661834757 n with h12 | h12
            · -- n > 7880735252661834757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07773 n (by omega) (by omega)
            · -- n <= 7880735252661834757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07772 n (by omega) (by omega)
          · -- n <= 7858485554889704341
            exact RamareSaouter2003.prime_interval_nat_ladder_c07771 n (by omega) (by omega)
        · -- n <= 7836298679467036721
          rcases Nat.lt_or_ge 7792112747232812389 n with h10 | h10
          · -- n > 7792112747232812389
            rcases Nat.lt_or_ge 7814174471561331233 n with h12 | h12
            · -- n > 7814174471561331233
              exact RamareSaouter2003.prime_interval_nat_ladder_c07770 n (by omega) (by omega)
            · -- n <= 7814174471561331233
              exact RamareSaouter2003.prime_interval_nat_ladder_c07769 n (by omega) (by omega)
          · -- n <= 7792112747232812389
            exact RamareSaouter2003.prime_interval_nat_ladder_c07768 n (by omega) (by omega)
      · -- n <= 7770113224424102369
        rcases Nat.lt_or_ge 7704486840280639477 n with h8 | h8
        · -- n > 7704486840280639477
          rcases Nat.lt_or_ge 7726300594212059999 n with h10 | h10
          · -- n > 7726300594212059999
            rcases Nat.lt_or_ge 7748175759388131211 n with h12 | h12
            · -- n > 7748175759388131211
              exact RamareSaouter2003.prime_interval_nat_ladder_c07767 n (by omega) (by omega)
            · -- n <= 7748175759388131211
              exact RamareSaouter2003.prime_interval_nat_ladder_c07766 n (by omega) (by omega)
          · -- n <= 7726300594212059999
            exact RamareSaouter2003.prime_interval_nat_ladder_c07765 n (by omega) (by omega)
        · -- n <= 7704486840280639477
          rcases Nat.lt_or_ge 7661044107201706409 n with h10 | h10
          · -- n > 7661044107201706409
            rcases Nat.lt_or_ge 7682734767678175787 n with h12 | h12
            · -- n > 7682734767678175787
              exact RamareSaouter2003.prime_interval_nat_ladder_c07764 n (by omega) (by omega)
            · -- n <= 7682734767678175787
              exact RamareSaouter2003.prime_interval_nat_ladder_c07763 n (by omega) (by omega)
          · -- n <= 7661044107201706409
            exact RamareSaouter2003.prime_interval_nat_ladder_c07762 n (by omega) (by omega)
  · -- n <= 7639414894591921261
    rcases Nat.lt_or_ge 7384575971553946219 n with h4 | h4
    · -- n > 7384575971553946219
      rcases Nat.lt_or_ge 7510914413387407391 n with h6 | h6
      · -- n > 7510914413387407391
        rcases Nat.lt_or_ge 7574892110612523847 n with h8 | h8
        · -- n > 7574892110612523847
          rcases Nat.lt_or_ge 7596338939367781973 n with h10 | h10
          · -- n > 7596338939367781973
            rcases Nat.lt_or_ge 7617846513134661227 n with h12 | h12
            · -- n > 7617846513134661227
              exact RamareSaouter2003.prime_interval_nat_ladder_c07761 n (by omega) (by omega)
            · -- n <= 7617846513134661227
              exact RamareSaouter2003.prime_interval_nat_ladder_c07760 n (by omega) (by omega)
          · -- n <= 7596338939367781973
            exact RamareSaouter2003.prime_interval_nat_ladder_c07759 n (by omega) (by omega)
        · -- n <= 7574892110612523847
          rcases Nat.lt_or_ge 7532180107786813511 n with h10 | h10
          · -- n > 7532180107786813511
            rcases Nat.lt_or_ge 7553506013757763883 n with h12 | h12
            · -- n > 7553506013757763883
              exact RamareSaouter2003.prime_interval_nat_ladder_c07758 n (by omega) (by omega)
            · -- n <= 7553506013757763883
              exact RamareSaouter2003.prime_interval_nat_ladder_c07757 n (by omega) (by omega)
          · -- n <= 7532180107786813511
            exact RamareSaouter2003.prime_interval_nat_ladder_c07756 n (by omega) (by omega)
      · -- n <= 7510914413387407391
        rcases Nat.lt_or_ge 7447477425112927649 n with h8 | h8
        · -- n > 7447477425112927649
          rcases Nat.lt_or_ge 7468563297784133873 n with h10 | h10
          · -- n > 7468563297784133873
            rcases Nat.lt_or_ge 7489708825289056523 n with h12 | h12
            · -- n > 7489708825289056523
              exact RamareSaouter2003.prime_interval_nat_ladder_c07755 n (by omega) (by omega)
            · -- n <= 7489708825289056523
              exact RamareSaouter2003.prime_interval_nat_ladder_c07754 n (by omega) (by omega)
          · -- n <= 7468563297784133873
            exact RamareSaouter2003.prime_interval_nat_ladder_c07753 n (by omega) (by omega)
        · -- n <= 7447477425112927649
          rcases Nat.lt_or_ge 7405483909273856047 n with h10 | h10
          · -- n > 7405483909273856047
            rcases Nat.lt_or_ge 7426450884061845721 n with h12 | h12
            · -- n > 7426450884061845721
              exact RamareSaouter2003.prime_interval_nat_ladder_c07752 n (by omega) (by omega)
            · -- n <= 7426450884061845721
              exact RamareSaouter2003.prime_interval_nat_ladder_c07751 n (by omega) (by omega)
          · -- n <= 7405483909273856047
            exact RamareSaouter2003.prime_interval_nat_ladder_c07750 n (by omega) (by omega)
    · -- n <= 7384575971553946219
      rcases Nat.lt_or_ge 7260362750774603287 n with h6 | h6
      · -- n > 7260362750774603287
        rcases Nat.lt_or_ge 7322205897532738309 n with h8 | h8
        · -- n > 7322205897532738309
          rcases Nat.lt_or_ge 7342937271885250591 n with h10 | h10
          · -- n > 7342937271885250591
            rcases Nat.lt_or_ge 7363727135967060121 n with h12 | h12
            · -- n > 7363727135967060121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07749 n (by omega) (by omega)
            · -- n <= 7363727135967060121
              exact RamareSaouter2003.prime_interval_nat_ladder_c07748 n (by omega) (by omega)
          · -- n <= 7342937271885250591
            exact RamareSaouter2003.prime_interval_nat_ladder_c07747 n (by omega) (by omega)
        · -- n <= 7322205897532738309
          rcases Nat.lt_or_ge 7280918628723599677 n with h10 | h10
          · -- n > 7280918628723599677
            rcases Nat.lt_or_ge 7301533115377822619 n with h12 | h12
            · -- n > 7301533115377822619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07746 n (by omega) (by omega)
            · -- n <= 7301533115377822619
              exact RamareSaouter2003.prime_interval_nat_ladder_c07745 n (by omega) (by omega)
          · -- n <= 7280918628723599677
            exact RamareSaouter2003.prime_interval_nat_ladder_c07744 n (by omega) (by omega)
      · -- n <= 7260362750774603287
        rcases Nat.lt_or_ge 7199041555224444637 n with h8 | h8
        · -- n > 7199041555224444637
          rcases Nat.lt_or_ge 7219424107895158591 n with h10 | h10
          · -- n > 7219424107895158591
            rcases Nat.lt_or_ge 7239864517672070759 n with h12 | h12
            · -- n > 7239864517672070759
              exact RamareSaouter2003.prime_interval_nat_ladder_c07743 n (by omega) (by omega)
            · -- n <= 7239864517672070759
              exact RamareSaouter2003.prime_interval_nat_ladder_c07742 n (by omega) (by omega)
          · -- n <= 7219424107895158591
            exact RamareSaouter2003.prime_interval_nat_ladder_c07741 n (by omega) (by omega)
        · -- n <= 7199041555224444637
          rcases Nat.lt_or_ge 7158448790898264383 n with h10 | h10
          · -- n > 7158448790898264383
            rcases Nat.lt_or_ge 7178716495544331571 n with h12 | h12
            · -- n > 7178716495544331571
              exact RamareSaouter2003.prime_interval_nat_ladder_c07740 n (by omega) (by omega)
            · -- n <= 7178716495544331571
              exact RamareSaouter2003.prime_interval_nat_ladder_c07739 n (by omega) (by omega)
          · -- n <= 7158448790898264383
            exact RamareSaouter2003.prime_interval_nat_ladder_c07738 n (by omega) (by omega)
