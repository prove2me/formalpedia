-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T23:56:54.451731+00:00
-- url     : https://prove2.me/submissions/316282c4-0306-499d-b5a0-1c25c415ac8c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00850

theorem solution (n : Nat)
    (hn : 63861919811 < n) (hupper : n <= 71627919427) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 67631043563 n with h2 | h2
  · -- n > 67631043563
    rcases Nat.lt_or_ge 69520274137 n with h4 | h4
    · -- n > 69520274137
      rcases Nat.lt_or_ge 70485039307 n with h6 | h6
      · -- n > 70485039307
        rcases Nat.lt_or_ge 70972544581 n with h8 | h8
        · -- n > 70972544581
          rcases Nat.lt_or_ge 71299462109 n with h10 | h10
          · -- n > 71299462109
            rcases Nat.lt_or_ge 71463497797 n with h12 | h12
            · -- n > 71463497797
              exact RamareSaouter2003.prime_interval_nat_ladder_c00850 n (by omega) (by omega)
            · -- n <= 71463497797
              exact RamareSaouter2003.prime_interval_nat_ladder_c00849 n (by omega) (by omega)
          · -- n <= 71299462109
            rcases Nat.lt_or_ge 71135811343 n with h12 | h12
            · -- n > 71135811343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00848 n (by omega) (by omega)
            · -- n <= 71135811343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00847 n (by omega) (by omega)
        · -- n <= 70972544581
          rcases Nat.lt_or_ge 70647159487 n with h10 | h10
          · -- n > 70647159487
            rcases Nat.lt_or_ge 70809660931 n with h12 | h12
            · -- n > 70809660931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00846 n (by omega) (by omega)
            · -- n <= 70809660931
              exact RamareSaouter2003.prime_interval_nat_ladder_c00845 n (by omega) (by omega)
          · -- n <= 70647159487
            exact RamareSaouter2003.prime_interval_nat_ladder_c00844 n (by omega) (by omega)
      · -- n <= 70485039307
        rcases Nat.lt_or_ge 70000957339 n with h8 | h8
        · -- n > 70000957339
          rcases Nat.lt_or_ge 70161939157 n with h10 | h10
          · -- n > 70161939157
            rcases Nat.lt_or_ge 70323299489 n with h12 | h12
            · -- n > 70323299489
              exact RamareSaouter2003.prime_interval_nat_ladder_c00843 n (by omega) (by omega)
            · -- n <= 70323299489
              exact RamareSaouter2003.prime_interval_nat_ladder_c00842 n (by omega) (by omega)
          · -- n <= 70161939157
            exact RamareSaouter2003.prime_interval_nat_ladder_c00841 n (by omega) (by omega)
        · -- n <= 70000957339
          rcases Nat.lt_or_ge 69680125789 n with h10 | h10
          · -- n > 69680125789
            rcases Nat.lt_or_ge 69840353161 n with h12 | h12
            · -- n > 69840353161
              exact RamareSaouter2003.prime_interval_nat_ladder_c00840 n (by omega) (by omega)
            · -- n <= 69840353161
              exact RamareSaouter2003.prime_interval_nat_ladder_c00839 n (by omega) (by omega)
          · -- n <= 69680125789
            exact RamareSaouter2003.prime_interval_nat_ladder_c00838 n (by omega) (by omega)
    · -- n <= 69520274137
      rcases Nat.lt_or_ge 68569006511 n with h6 | h6
      · -- n > 68569006511
        rcases Nat.lt_or_ge 69042965207 n with h8 | h8
        · -- n > 69042965207
          rcases Nat.lt_or_ge 69201694769 n with h10 | h10
          · -- n > 69201694769
            rcases Nat.lt_or_ge 69360797459 n with h12 | h12
            · -- n > 69360797459
              exact RamareSaouter2003.prime_interval_nat_ladder_c00837 n (by omega) (by omega)
            · -- n <= 69360797459
              exact RamareSaouter2003.prime_interval_nat_ladder_c00836 n (by omega) (by omega)
          · -- n <= 69201694769
            exact RamareSaouter2003.prime_interval_nat_ladder_c00835 n (by omega) (by omega)
        · -- n <= 69042965207
          rcases Nat.lt_or_ge 68726621983 n with h10 | h10
          · -- n > 68726621983
            rcases Nat.lt_or_ge 68884607933 n with h12 | h12
            · -- n > 68884607933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00834 n (by omega) (by omega)
            · -- n <= 68884607933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00833 n (by omega) (by omega)
          · -- n <= 68726621983
            exact RamareSaouter2003.prime_interval_nat_ladder_c00832 n (by omega) (by omega)
      · -- n <= 68569006511
        rcases Nat.lt_or_ge 68098373869 n with h8 | h8
        · -- n > 68098373869
          rcases Nat.lt_or_ge 68254883321 n with h10 | h10
          · -- n > 68254883321
            rcases Nat.lt_or_ge 68411760559 n with h12 | h12
            · -- n > 68411760559
              exact RamareSaouter2003.prime_interval_nat_ladder_c00831 n (by omega) (by omega)
            · -- n <= 68411760559
              exact RamareSaouter2003.prime_interval_nat_ladder_c00830 n (by omega) (by omega)
          · -- n <= 68254883321
            exact RamareSaouter2003.prime_interval_nat_ladder_c00829 n (by omega) (by omega)
        · -- n <= 68098373869
          rcases Nat.lt_or_ge 67786454881 n with h10 | h10
          · -- n > 67786454881
            rcases Nat.lt_or_ge 67942231369 n with h12 | h12
            · -- n > 67942231369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00828 n (by omega) (by omega)
            · -- n <= 67942231369
              exact RamareSaouter2003.prime_interval_nat_ladder_c00827 n (by omega) (by omega)
          · -- n <= 67786454881
            exact RamareSaouter2003.prime_interval_nat_ladder_c00826 n (by omega) (by omega)
  · -- n <= 67631043563
    rcases Nat.lt_or_ge 65643531917 n with h4 | h4
    · -- n > 65643531917
      rcases Nat.lt_or_ge 66553315909 n with h6 | h6
      · -- n > 66553315909
        rcases Nat.lt_or_ge 67013032523 n with h8 | h8
        · -- n > 67013032523
          rcases Nat.lt_or_ge 67321312951 n with h10 | h10
          · -- n > 67321312951
            rcases Nat.lt_or_ge 67475996551 n with h12 | h12
            · -- n > 67475996551
              exact RamareSaouter2003.prime_interval_nat_ladder_c00825 n (by omega) (by omega)
            · -- n <= 67475996551
              exact RamareSaouter2003.prime_interval_nat_ladder_c00824 n (by omega) (by omega)
          · -- n <= 67321312951
            rcases Nat.lt_or_ge 67166991907 n with h12 | h12
            · -- n > 67166991907
              exact RamareSaouter2003.prime_interval_nat_ladder_c00823 n (by omega) (by omega)
            · -- n <= 67166991907
              exact RamareSaouter2003.prime_interval_nat_ladder_c00822 n (by omega) (by omega)
        · -- n <= 67013032523
          rcases Nat.lt_or_ge 66706195421 n with h10 | h10
          · -- n > 66706195421
            rcases Nat.lt_or_ge 66859433983 n with h12 | h12
            · -- n > 66859433983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00821 n (by omega) (by omega)
            · -- n <= 66859433983
              exact RamareSaouter2003.prime_interval_nat_ladder_c00820 n (by omega) (by omega)
          · -- n <= 66706195421
            exact RamareSaouter2003.prime_interval_nat_ladder_c00819 n (by omega) (by omega)
      · -- n <= 66553315909
        rcases Nat.lt_or_ge 66096823417 n with h8 | h8
        · -- n > 66096823417
          rcases Nat.lt_or_ge 66248630807 n with h10 | h10
          · -- n > 66248630807
            rcases Nat.lt_or_ge 66400794697 n with h12 | h12
            · -- n > 66400794697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00818 n (by omega) (by omega)
            · -- n <= 66400794697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00817 n (by omega) (by omega)
          · -- n <= 66248630807
            exact RamareSaouter2003.prime_interval_nat_ladder_c00816 n (by omega) (by omega)
        · -- n <= 66096823417
          rcases Nat.lt_or_ge 65794274879 n with h10 | h10
          · -- n > 65794274879
            rcases Nat.lt_or_ge 65945371781 n with h12 | h12
            · -- n > 65945371781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00815 n (by omega) (by omega)
            · -- n <= 65945371781
              exact RamareSaouter2003.prime_interval_nat_ladder_c00814 n (by omega) (by omega)
          · -- n <= 65794274879
            exact RamareSaouter2003.prime_interval_nat_ladder_c00813 n (by omega) (by omega)
    · -- n <= 65643531917
      rcases Nat.lt_or_ge 64746460393 n with h6 | h6
      · -- n > 64746460393
        rcases Nat.lt_or_ge 65193418489 n with h8 | h8
        · -- n > 65193418489
          rcases Nat.lt_or_ge 65343104579 n with h10 | h10
          · -- n > 65343104579
            rcases Nat.lt_or_ge 65493142111 n with h12 | h12
            · -- n > 65493142111
              exact RamareSaouter2003.prime_interval_nat_ladder_c00812 n (by omega) (by omega)
            · -- n <= 65493142111
              exact RamareSaouter2003.prime_interval_nat_ladder_c00811 n (by omega) (by omega)
          · -- n <= 65343104579
            exact RamareSaouter2003.prime_interval_nat_ladder_c00810 n (by omega) (by omega)
        · -- n <= 65193418489
          rcases Nat.lt_or_ge 64895097193 n with h10 | h10
          · -- n > 64895097193
            rcases Nat.lt_or_ge 65044082951 n with h12 | h12
            · -- n > 65044082951
              exact RamareSaouter2003.prime_interval_nat_ladder_c00809 n (by omega) (by omega)
            · -- n <= 65044082951
              exact RamareSaouter2003.prime_interval_nat_ladder_c00808 n (by omega) (by omega)
          · -- n <= 64895097193
            exact RamareSaouter2003.prime_interval_nat_ladder_c00807 n (by omega) (by omega)
      · -- n <= 64746460393
        rcases Nat.lt_or_ge 64302634919 n with h8 | h8
        · -- n > 64302634919
          rcases Nat.lt_or_ge 64450230043 n with h10 | h10
          · -- n > 64450230043
            rcases Nat.lt_or_ge 64598171593 n with h12 | h12
            · -- n > 64598171593
              exact RamareSaouter2003.prime_interval_nat_ladder_c00806 n (by omega) (by omega)
            · -- n <= 64598171593
              exact RamareSaouter2003.prime_interval_nat_ladder_c00805 n (by omega) (by omega)
          · -- n <= 64450230043
            exact RamareSaouter2003.prime_interval_nat_ladder_c00804 n (by omega) (by omega)
        · -- n <= 64302634919
          rcases Nat.lt_or_ge 64008480589 n with h10 | h10
          · -- n > 64008480589
            rcases Nat.lt_or_ge 64155385381 n with h12 | h12
            · -- n > 64155385381
              exact RamareSaouter2003.prime_interval_nat_ladder_c00803 n (by omega) (by omega)
            · -- n <= 64155385381
              exact RamareSaouter2003.prime_interval_nat_ladder_c00802 n (by omega) (by omega)
          · -- n <= 64008480589
            exact RamareSaouter2003.prime_interval_nat_ladder_c00801 n (by omega) (by omega)
