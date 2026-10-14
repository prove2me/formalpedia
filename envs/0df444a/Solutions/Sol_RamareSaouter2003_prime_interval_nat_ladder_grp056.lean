-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T00:21:44.707432+00:00
-- url     : https://prove2.me/submissions/55b4c46d-ca7f-4c4d-99d2-e1a1bf809dc6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02800

theorem solution (n : Nat)
    (hn : 8179930630579 < n) (hupper : n <= 9255959571041) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 8701327899161 n with h2 | h2
  · -- n > 8701327899161
    rcases Nat.lt_or_ge 8963276084263 n with h4 | h4
    · -- n > 8963276084263
      rcases Nat.lt_or_ge 9097192675973 n with h6 | h6
      · -- n > 9097192675973
        rcases Nat.lt_or_ge 9164899410883 n with h8 | h8
        · -- n > 9164899410883
          rcases Nat.lt_or_ge 9210316955507 n with h10 | h10
          · -- n > 9210316955507
            rcases Nat.lt_or_ge 9233110059731 n with h12 | h12
            · -- n > 9233110059731
              exact RamareSaouter2003.prime_interval_nat_ladder_c02800 n (by omega) (by omega)
            · -- n <= 9233110059731
              exact RamareSaouter2003.prime_interval_nat_ladder_c02799 n (by omega) (by omega)
          · -- n <= 9210316955507
            rcases Nat.lt_or_ge 9187580118869 n with h12 | h12
            · -- n > 9187580118869
              exact RamareSaouter2003.prime_interval_nat_ladder_c02798 n (by omega) (by omega)
            · -- n <= 9187580118869
              exact RamareSaouter2003.prime_interval_nat_ladder_c02797 n (by omega) (by omega)
        · -- n <= 9164899410883
          rcases Nat.lt_or_ge 9119705827513 n with h10 | h10
          · -- n > 9119705827513
            rcases Nat.lt_or_ge 9142274693197 n with h12 | h12
            · -- n > 9142274693197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02796 n (by omega) (by omega)
            · -- n <= 9142274693197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02795 n (by omega) (by omega)
          · -- n <= 9119705827513
            exact RamareSaouter2003.prime_interval_nat_ladder_c02794 n (by omega) (by omega)
      · -- n <= 9097192675973
        rcases Nat.lt_or_ge 9029986132151 n with h8 | h8
        · -- n > 9029986132151
          rcases Nat.lt_or_ge 9052332965213 n with h10 | h10
          · -- n > 9052332965213
            rcases Nat.lt_or_ge 9074735100917 n with h12 | h12
            · -- n > 9074735100917
              exact RamareSaouter2003.prime_interval_nat_ladder_c02793 n (by omega) (by omega)
            · -- n <= 9074735100917
              exact RamareSaouter2003.prime_interval_nat_ladder_c02792 n (by omega) (by omega)
          · -- n <= 9052332965213
            exact RamareSaouter2003.prime_interval_nat_ladder_c02791 n (by omega) (by omega)
        · -- n <= 9029986132151
          rcases Nat.lt_or_ge 8985457827653 n with h10 | h10
          · -- n > 8985457827653
            rcases Nat.lt_or_ge 9007694464991 n with h12 | h12
            · -- n > 9007694464991
              exact RamareSaouter2003.prime_interval_nat_ladder_c02790 n (by omega) (by omega)
            · -- n <= 9007694464991
              exact RamareSaouter2003.prime_interval_nat_ladder_c02789 n (by omega) (by omega)
          · -- n <= 8985457827653
            exact RamareSaouter2003.prime_interval_nat_ladder_c02788 n (by omega) (by omega)
    · -- n <= 8963276084263
      rcases Nat.lt_or_ge 8831330831711 n with h6 | h6
      · -- n > 8831330831711
        rcases Nat.lt_or_ge 8897058864341 n with h8 | h8
        · -- n > 8897058864341
          rcases Nat.lt_or_ge 8919076737643 n with h10 | h10
          · -- n > 8919076737643
            rcases Nat.lt_or_ge 8941149099361 n with h12 | h12
            · -- n > 8941149099361
              exact RamareSaouter2003.prime_interval_nat_ladder_c02787 n (by omega) (by omega)
            · -- n <= 8941149099361
              exact RamareSaouter2003.prime_interval_nat_ladder_c02786 n (by omega) (by omega)
          · -- n <= 8919076737643
            exact RamareSaouter2003.prime_interval_nat_ladder_c02785 n (by omega) (by omega)
        · -- n <= 8897058864341
          rcases Nat.lt_or_ge 8853186045463 n with h10 | h10
          · -- n > 8853186045463
            rcases Nat.lt_or_ge 8875095345041 n with h12 | h12
            · -- n > 8875095345041
              exact RamareSaouter2003.prime_interval_nat_ladder_c02784 n (by omega) (by omega)
            · -- n <= 8875095345041
              exact RamareSaouter2003.prime_interval_nat_ladder_c02783 n (by omega) (by omega)
          · -- n <= 8853186045463
            exact RamareSaouter2003.prime_interval_nat_ladder_c02782 n (by omega) (by omega)
      · -- n <= 8831330831711
        rcases Nat.lt_or_ge 8766088372253 n with h8 | h8
        · -- n > 8766088372253
          rcases Nat.lt_or_ge 8787782128129 n with h10 | h10
          · -- n > 8787782128129
            rcases Nat.lt_or_ge 8809529570327 n with h12 | h12
            · -- n > 8809529570327
              exact RamareSaouter2003.prime_interval_nat_ladder_c02781 n (by omega) (by omega)
            · -- n <= 8809529570327
              exact RamareSaouter2003.prime_interval_nat_ladder_c02780 n (by omega) (by omega)
          · -- n <= 8787782128129
            exact RamareSaouter2003.prime_interval_nat_ladder_c02779 n (by omega) (by omega)
        · -- n <= 8766088372253
          rcases Nat.lt_or_ge 8722861389691 n with h10 | h10
          · -- n > 8722861389691
            rcases Nat.lt_or_ge 8744448170177 n with h12 | h12
            · -- n > 8744448170177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02778 n (by omega) (by omega)
            · -- n <= 8744448170177
              exact RamareSaouter2003.prime_interval_nat_ladder_c02777 n (by omega) (by omega)
          · -- n <= 8722861389691
            exact RamareSaouter2003.prime_interval_nat_ladder_c02776 n (by omega) (by omega)
  · -- n <= 8701327899161
    rcases Nat.lt_or_ge 8426182467809 n with h4 | h4
    · -- n > 8426182467809
      rcases Nat.lt_or_ge 8552074566521 n with h6 | h6
      · -- n > 8552074566521
        rcases Nat.lt_or_ge 8615724207263 n with h8 | h8
        · -- n > 8615724207263
          rcases Nat.lt_or_ge 8658420260953 n with h10 | h10
          · -- n > 8658420260953
            rcases Nat.lt_or_ge 8679847566623 n with h12 | h12
            · -- n > 8679847566623
              exact RamareSaouter2003.prime_interval_nat_ladder_c02775 n (by omega) (by omega)
            · -- n <= 8679847566623
              exact RamareSaouter2003.prime_interval_nat_ladder_c02774 n (by omega) (by omega)
          · -- n <= 8658420260953
            rcases Nat.lt_or_ge 8637045851321 n with h12 | h12
            · -- n > 8637045851321
              exact RamareSaouter2003.prime_interval_nat_ladder_c02773 n (by omega) (by omega)
            · -- n <= 8637045851321
              exact RamareSaouter2003.prime_interval_nat_ladder_c02772 n (by omega) (by omega)
        · -- n <= 8615724207263
          rcases Nat.lt_or_ge 8573238694543 n with h10 | h10
          · -- n > 8573238694543
            rcases Nat.lt_or_ge 8594455198229 n with h12 | h12
            · -- n > 8594455198229
              exact RamareSaouter2003.prime_interval_nat_ladder_c02771 n (by omega) (by omega)
            · -- n <= 8594455198229
              exact RamareSaouter2003.prime_interval_nat_ladder_c02770 n (by omega) (by omega)
          · -- n <= 8573238694543
            exact RamareSaouter2003.prime_interval_nat_ladder_c02769 n (by omega) (by omega)
      · -- n <= 8552074566521
        rcases Nat.lt_or_ge 8488895144531 n with h8 | h8
        · -- n > 8488895144531
          rcases Nat.lt_or_ge 8509902920269 n with h10 | h10
          · -- n > 8509902920269
            rcases Nat.lt_or_ge 8530962684721 n with h12 | h12
            · -- n > 8530962684721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02768 n (by omega) (by omega)
            · -- n <= 8530962684721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02767 n (by omega) (by omega)
          · -- n <= 8509902920269
            exact RamareSaouter2003.prime_interval_nat_ladder_c02766 n (by omega) (by omega)
        · -- n <= 8488895144531
          rcases Nat.lt_or_ge 8447035046257 n with h10 | h10
          · -- n > 8447035046257
            rcases Nat.lt_or_ge 8467939229261 n with h12 | h12
            · -- n > 8467939229261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02765 n (by omega) (by omega)
            · -- n <= 8467939229261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02764 n (by omega) (by omega)
          · -- n <= 8447035046257
            exact RamareSaouter2003.prime_interval_nat_ladder_c02763 n (by omega) (by omega)
    · -- n <= 8426182467809
      rcases Nat.lt_or_ge 8302143582763 n with h6 | h6
      · -- n > 8302143582763
        rcases Nat.lt_or_ge 8363933088139 n with h8 | h8
        · -- n > 8363933088139
          rcases Nat.lt_or_ge 8384631615653 n with h10 | h10
          · -- n > 8384631615653
            rcases Nat.lt_or_ge 8405381366593 n with h12 | h12
            · -- n > 8405381366593
              exact RamareSaouter2003.prime_interval_nat_ladder_c02762 n (by omega) (by omega)
            · -- n <= 8405381366593
              exact RamareSaouter2003.prime_interval_nat_ladder_c02761 n (by omega) (by omega)
          · -- n <= 8384631615653
            exact RamareSaouter2003.prime_interval_nat_ladder_c02760 n (by omega) (by omega)
        · -- n <= 8363933088139
          rcases Nat.lt_or_ge 8322689197657 n with h10 | h10
          · -- n > 8322689197657
            rcases Nat.lt_or_ge 8343285657571 n with h12 | h12
            · -- n > 8343285657571
              exact RamareSaouter2003.prime_interval_nat_ladder_c02759 n (by omega) (by omega)
            · -- n <= 8343285657571
              exact RamareSaouter2003.prime_interval_nat_ladder_c02758 n (by omega) (by omega)
          · -- n <= 8322689197657
            exact RamareSaouter2003.prime_interval_nat_ladder_c02757 n (by omega) (by omega)
      · -- n <= 8302143582763
        rcases Nat.lt_or_ge 8240810554297 n with h8 | h8
        · -- n > 8240810554297
          rcases Nat.lt_or_ge 8261204386157 n with h10 | h10
          · -- n > 8261204386157
            rcases Nat.lt_or_ge 8281648687313 n with h12 | h12
            · -- n > 8281648687313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02756 n (by omega) (by omega)
            · -- n <= 8281648687313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02755 n (by omega) (by omega)
          · -- n <= 8261204386157
            exact RamareSaouter2003.prime_interval_nat_ladder_c02754 n (by omega) (by omega)
        · -- n <= 8240810554297
          rcases Nat.lt_or_ge 8200173800633 n with h10 | h10
          · -- n > 8200173800633
            rcases Nat.lt_or_ge 8220467067193 n with h12 | h12
            · -- n > 8220467067193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02753 n (by omega) (by omega)
            · -- n <= 8220467067193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02752 n (by omega) (by omega)
          · -- n <= 8200173800633
            exact RamareSaouter2003.prime_interval_nat_ladder_c02751 n (by omega) (by omega)
