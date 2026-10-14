-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T23:50:05.431177+00:00
-- url     : https://prove2.me/submissions/e4cec6f4-255b-428f-9230-71d168f702a2

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02750

theorem solution (n : Nat)
    (hn : 7228992803521 < n) (hupper : n <= 8179930630579) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 7689776307847 n with h2 | h2
  · -- n > 7689776307847
    rcases Nat.lt_or_ge 7921272346717 n with h4 | h4
    · -- n > 7921272346717
      rcases Nat.lt_or_ge 8039620792331 n with h6 | h6
      · -- n > 8039620792331
        rcases Nat.lt_or_ge 8099456446451 n with h8 | h8
        · -- n > 8099456446451
          rcases Nat.lt_or_ge 8139594085577 n with h10 | h10
          · -- n > 8139594085577
            rcases Nat.lt_or_ge 8159737433389 n with h12 | h12
            · -- n > 8159737433389
              exact RamareSaouter2003.prime_interval_nat_ladder_c02750 n (by omega) (by omega)
            · -- n <= 8159737433389
              exact RamareSaouter2003.prime_interval_nat_ladder_c02749 n (by omega) (by omega)
          · -- n <= 8139594085577
            rcases Nat.lt_or_ge 8119500464197 n with h12 | h12
            · -- n > 8119500464197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02748 n (by omega) (by omega)
            · -- n <= 8119500464197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02747 n (by omega) (by omega)
        · -- n <= 8099456446451
          rcases Nat.lt_or_ge 8059516732511 n with h10 | h10
          · -- n > 8059516732511
            rcases Nat.lt_or_ge 8079461909899 n with h12 | h12
            · -- n > 8079461909899
              exact RamareSaouter2003.prime_interval_nat_ladder_c02746 n (by omega) (by omega)
            · -- n <= 8079461909899
              exact RamareSaouter2003.prime_interval_nat_ladder_c02745 n (by omega) (by omega)
          · -- n <= 8059516732511
            exact RamareSaouter2003.prime_interval_nat_ladder_c02744 n (by omega) (by omega)
      · -- n <= 8039620792331
        rcases Nat.lt_or_ge 7980227180999 n with h8 | h8
        · -- n > 7980227180999
          rcases Nat.lt_or_ge 7999976137771 n with h10 | h10
          · -- n > 7999976137771
            rcases Nat.lt_or_ge 8019773967839 n with h12 | h12
            · -- n > 8019773967839
              exact RamareSaouter2003.prime_interval_nat_ladder_c02743 n (by omega) (by omega)
            · -- n <= 8019773967839
              exact RamareSaouter2003.prime_interval_nat_ladder_c02742 n (by omega) (by omega)
          · -- n <= 7999976137771
            exact RamareSaouter2003.prime_interval_nat_ladder_c02741 n (by omega) (by omega)
        · -- n <= 7980227180999
          rcases Nat.lt_or_ge 7940875405657 n with h10 | h10
          · -- n > 7940875405657
            rcases Nat.lt_or_ge 7960526977049 n with h12 | h12
            · -- n > 7960526977049
              exact RamareSaouter2003.prime_interval_nat_ladder_c02740 n (by omega) (by omega)
            · -- n <= 7960526977049
              exact RamareSaouter2003.prime_interval_nat_ladder_c02739 n (by omega) (by omega)
          · -- n <= 7940875405657
            exact RamareSaouter2003.prime_interval_nat_ladder_c02738 n (by omega) (by omega)
    · -- n <= 7921272346717
      rcases Nat.lt_or_ge 7804666067183 n with h6 | h6
      · -- n > 7804666067183
        rcases Nat.lt_or_ge 7862753047997 n with h8 | h8
        · -- n > 7862753047997
          rcases Nat.lt_or_ge 7882211287283 n with h10 | h10
          · -- n > 7882211287283
            rcases Nat.lt_or_ge 7901717680391 n with h12 | h12
            · -- n > 7901717680391
              exact RamareSaouter2003.prime_interval_nat_ladder_c02737 n (by omega) (by omega)
            · -- n <= 7901717680391
              exact RamareSaouter2003.prime_interval_nat_ladder_c02736 n (by omega) (by omega)
          · -- n <= 7882211287283
            exact RamareSaouter2003.prime_interval_nat_ladder_c02735 n (by omega) (by omega)
        · -- n <= 7862753047997
          rcases Nat.lt_or_ge 7823980556473 n with h10 | h10
          · -- n > 7823980556473
            rcases Nat.lt_or_ge 7843342844011 n with h12 | h12
            · -- n > 7843342844011
              exact RamareSaouter2003.prime_interval_nat_ladder_c02734 n (by omega) (by omega)
            · -- n <= 7843342844011
              exact RamareSaouter2003.prime_interval_nat_ladder_c02733 n (by omega) (by omega)
          · -- n <= 7823980556473
            exact RamareSaouter2003.prime_interval_nat_ladder_c02732 n (by omega) (by omega)
      · -- n <= 7804666067183
        rcases Nat.lt_or_ge 7747008210493 n with h8 | h8
        · -- n > 7747008210493
          rcases Nat.lt_or_ge 7766180011853 n with h10 | h10
          · -- n > 7766180011853
            rcases Nat.lt_or_ge 7785399258181 n with h12 | h12
            · -- n > 7785399258181
              exact RamareSaouter2003.prime_interval_nat_ladder_c02731 n (by omega) (by omega)
            · -- n <= 7785399258181
              exact RamareSaouter2003.prime_interval_nat_ladder_c02730 n (by omega) (by omega)
          · -- n <= 7766180011853
            exact RamareSaouter2003.prime_interval_nat_ladder_c02729 n (by omega) (by omega)
        · -- n <= 7747008210493
          rcases Nat.lt_or_ge 7708806475283 n with h10 | h10
          · -- n > 7708806475283
            rcases Nat.lt_or_ge 7727883737237 n with h12 | h12
            · -- n > 7727883737237
              exact RamareSaouter2003.prime_interval_nat_ladder_c02728 n (by omega) (by omega)
            · -- n <= 7727883737237
              exact RamareSaouter2003.prime_interval_nat_ladder_c02727 n (by omega) (by omega)
          · -- n <= 7708806475283
            exact RamareSaouter2003.prime_interval_nat_ladder_c02726 n (by omega) (by omega)
  · -- n <= 7689776307847
    rcases Nat.lt_or_ge 7446617235679 n with h4 | h4
    · -- n > 7446617235679
      rcases Nat.lt_or_ge 7557874056277 n with h6 | h6
      · -- n > 7557874056277
        rcases Nat.lt_or_ge 7614124263617 n with h8 | h8
        · -- n > 7614124263617
          rcases Nat.lt_or_ge 7651856792033 n with h10 | h10
          · -- n > 7651856792033
            rcases Nat.lt_or_ge 7670793118733 n with h12 | h12
            · -- n > 7670793118733
              exact RamareSaouter2003.prime_interval_nat_ladder_c02725 n (by omega) (by omega)
            · -- n <= 7670793118733
              exact RamareSaouter2003.prime_interval_nat_ladder_c02724 n (by omega) (by omega)
          · -- n <= 7651856792033
            rcases Nat.lt_or_ge 7632967212067 n with h12 | h12
            · -- n > 7632967212067
              exact RamareSaouter2003.prime_interval_nat_ladder_c02723 n (by omega) (by omega)
            · -- n <= 7632967212067
              exact RamareSaouter2003.prime_interval_nat_ladder_c02722 n (by omega) (by omega)
        · -- n <= 7614124263617
          rcases Nat.lt_or_ge 7576577800291 n with h10 | h10
          · -- n > 7576577800291
            rcases Nat.lt_or_ge 7595327831177 n with h12 | h12
            · -- n > 7595327831177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02721 n (by omega) (by omega)
            · -- n <= 7595327831177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02720 n (by omega) (by omega)
          · -- n <= 7576577800291
            exact RamareSaouter2003.prime_interval_nat_ladder_c02719 n (by omega) (by omega)
      · -- n <= 7557874056277
        rcases Nat.lt_or_ge 7502039403493 n with h8 | h8
        · -- n > 7502039403493
          rcases Nat.lt_or_ge 7520604971669 n with h10 | h10
          · -- n > 7520604971669
            rcases Nat.lt_or_ge 7539216484741 n with h12 | h12
            · -- n > 7539216484741
              exact RamareSaouter2003.prime_interval_nat_ladder_c02718 n (by omega) (by omega)
            · -- n <= 7539216484741
              exact RamareSaouter2003.prime_interval_nat_ladder_c02717 n (by omega) (by omega)
          · -- n <= 7520604971669
            exact RamareSaouter2003.prime_interval_nat_ladder_c02716 n (by omega) (by omega)
        · -- n <= 7502039403493
          rcases Nat.lt_or_ge 7465045648589 n with h10 | h10
          · -- n > 7465045648589
            rcases Nat.lt_or_ge 7483519666813 n with h12 | h12
            · -- n > 7483519666813
              exact RamareSaouter2003.prime_interval_nat_ladder_c02715 n (by omega) (by omega)
            · -- n <= 7483519666813
              exact RamareSaouter2003.prime_interval_nat_ladder_c02714 n (by omega) (by omega)
          · -- n <= 7465045648589
            exact RamareSaouter2003.prime_interval_nat_ladder_c02713 n (by omega) (by omega)
    · -- n <= 7446617235679
      rcases Nat.lt_or_ge 7336998187633 n with h6 | h6
      · -- n > 7336998187633
        rcases Nat.lt_or_ge 7391604505247 n with h8 | h8
        · -- n > 7391604505247
          rcases Nat.lt_or_ge 7409896776179 n with h10 | h10
          · -- n > 7409896776179
            rcases Nat.lt_or_ge 7428234315673 n with h12 | h12
            · -- n > 7428234315673
              exact RamareSaouter2003.prime_interval_nat_ladder_c02712 n (by omega) (by omega)
            · -- n <= 7428234315673
              exact RamareSaouter2003.prime_interval_nat_ladder_c02711 n (by omega) (by omega)
          · -- n <= 7409896776179
            exact RamareSaouter2003.prime_interval_nat_ladder_c02710 n (by omega) (by omega)
        · -- n <= 7391604505247
          rcases Nat.lt_or_ge 7355155322321 n with h10 | h10
          · -- n > 7355155322321
            rcases Nat.lt_or_ge 7373357391121 n with h12 | h12
            · -- n > 7373357391121
              exact RamareSaouter2003.prime_interval_nat_ladder_c02709 n (by omega) (by omega)
            · -- n <= 7373357391121
              exact RamareSaouter2003.prime_interval_nat_ladder_c02708 n (by omega) (by omega)
          · -- n <= 7355155322321
            exact RamareSaouter2003.prime_interval_nat_ladder_c02707 n (by omega) (by omega)
      · -- n <= 7336998187633
        rcases Nat.lt_or_ge 7282795280567 n with h8 | h8
        · -- n > 7282795280567
          rcases Nat.lt_or_ge 7300818277211 n with h10 | h10
          · -- n > 7300818277211
            rcases Nat.lt_or_ge 7318885876111 n with h12 | h12
            · -- n > 7318885876111
              exact RamareSaouter2003.prime_interval_nat_ladder_c02706 n (by omega) (by omega)
            · -- n <= 7318885876111
              exact RamareSaouter2003.prime_interval_nat_ladder_c02705 n (by omega) (by omega)
          · -- n <= 7300818277211
            exact RamareSaouter2003.prime_interval_nat_ladder_c02704 n (by omega) (by omega)
        · -- n <= 7282795280567
          rcases Nat.lt_or_ge 7246882653389 n with h10 | h10
          · -- n > 7246882653389
            rcases Nat.lt_or_ge 7264816775897 n with h12 | h12
            · -- n > 7264816775897
              exact RamareSaouter2003.prime_interval_nat_ladder_c02703 n (by omega) (by omega)
            · -- n <= 7264816775897
              exact RamareSaouter2003.prime_interval_nat_ladder_c02702 n (by omega) (by omega)
          · -- n <= 7246882653389
            exact RamareSaouter2003.prime_interval_nat_ladder_c02701 n (by omega) (by omega)
