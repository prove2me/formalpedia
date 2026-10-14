-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T00:32:02.664945+00:00
-- url     : https://prove2.me/submissions/8968b997-ec97-453b-8196-b6659c670122

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02801
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02802
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02803
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02804
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02805
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02806
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02807
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02808
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02809
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02810
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02811
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02812
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02813
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02814
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02815
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02816
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02817
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02818
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02819
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02820
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02821
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02822
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02823
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02824
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02825
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02826
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02827
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02828
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02829
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02830
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02831
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02832
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02833
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02834
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02835
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02850

theorem solution (n : Nat)
    (hn : 9255959571041 < n) (hupper : n <= 10473534734783) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 9845944041601 n with h2 | h2
  · -- n > 9845944041601
    rcases Nat.lt_or_ge 10142350199363 n with h4 | h4
    · -- n > 10142350199363
      rcases Nat.lt_or_ge 10293882848593 n with h6 | h6
      · -- n > 10293882848593
        rcases Nat.lt_or_ge 10370496065947 n with h8 | h8
        · -- n > 10370496065947
          rcases Nat.lt_or_ge 10421888061367 n with h10 | h10
          · -- n > 10421888061367
            rcases Nat.lt_or_ge 10447679484601 n with h12 | h12
            · -- n > 10447679484601
              exact RamareSaouter2003.prime_interval_nat_ladder_c02850 n (by omega) (by omega)
            · -- n <= 10447679484601
              exact RamareSaouter2003.prime_interval_nat_ladder_c02849 n (by omega) (by omega)
          · -- n <= 10421888061367
            rcases Nat.lt_or_ge 10396160307571 n with h12 | h12
            · -- n > 10396160307571
              exact RamareSaouter2003.prime_interval_nat_ladder_c02848 n (by omega) (by omega)
            · -- n <= 10396160307571
              exact RamareSaouter2003.prime_interval_nat_ladder_c02847 n (by omega) (by omega)
        · -- n <= 10370496065947
          rcases Nat.lt_or_ge 10319357492687 n with h10 | h10
          · -- n > 10319357492687
            rcases Nat.lt_or_ge 10344895179791 n with h12 | h12
            · -- n > 10344895179791
              exact RamareSaouter2003.prime_interval_nat_ladder_c02846 n (by omega) (by omega)
            · -- n <= 10344895179791
              exact RamareSaouter2003.prime_interval_nat_ladder_c02845 n (by omega) (by omega)
          · -- n <= 10319357492687
            exact RamareSaouter2003.prime_interval_nat_ladder_c02844 n (by omega) (by omega)
      · -- n <= 10293882848593
        rcases Nat.lt_or_ge 10217835620287 n with h8 | h8
        · -- n > 10217835620287
          rcases Nat.lt_or_ge 10243122067499 n with h10 | h10
          · -- n > 10243122067499
            rcases Nat.lt_or_ge 10268471092073 n with h12 | h12
            · -- n > 10268471092073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02843 n (by omega) (by omega)
            · -- n <= 10268471092073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02842 n (by omega) (by omega)
          · -- n <= 10243122067499
            exact RamareSaouter2003.prime_interval_nat_ladder_c02841 n (by omega) (by omega)
        · -- n <= 10217835620287
          rcases Nat.lt_or_ge 10167449840161 n with h10 | h10
          · -- n > 10167449840161
            rcases Nat.lt_or_ge 10192611595931 n with h12 | h12
            · -- n > 10192611595931
              exact RamareSaouter2003.prime_interval_nat_ladder_c02840 n (by omega) (by omega)
            · -- n <= 10192611595931
              exact RamareSaouter2003.prime_interval_nat_ladder_c02839 n (by omega) (by omega)
          · -- n <= 10167449840161
            exact RamareSaouter2003.prime_interval_nat_ladder_c02838 n (by omega) (by omega)
    · -- n <= 10142350199363
      rcases Nat.lt_or_ge 9993048209293 n with h6 | h6
      · -- n > 9993048209293
        rcases Nat.lt_or_ge 10067422435613 n with h8 | h8
        · -- n > 10067422435613
          rcases Nat.lt_or_ge 10092336649909 n with h10 | h10
          · -- n > 10092336649909
            rcases Nat.lt_or_ge 10117312520257 n with h12 | h12
            · -- n > 10117312520257
              exact RamareSaouter2003.prime_interval_nat_ladder_c02837 n (by omega) (by omega)
            · -- n <= 10117312520257
              exact RamareSaouter2003.prime_interval_nat_ladder_c02836 n (by omega) (by omega)
          · -- n <= 10092336649909
            exact RamareSaouter2003.prime_interval_nat_ladder_c02835 n (by omega) (by omega)
        · -- n <= 10067422435613
          rcases Nat.lt_or_ge 10017778367029 n with h10 | h10
          · -- n > 10017778367029
            rcases Nat.lt_or_ge 10042569725249 n with h12 | h12
            · -- n > 10042569725249
              exact RamareSaouter2003.prime_interval_nat_ladder_c02834 n (by omega) (by omega)
            · -- n <= 10042569725249
              exact RamareSaouter2003.prime_interval_nat_ladder_c02833 n (by omega) (by omega)
          · -- n <= 10017778367029
            exact RamareSaouter2003.prime_interval_nat_ladder_c02832 n (by omega) (by omega)
      · -- n <= 9993048209293
        rcases Nat.lt_or_ge 9919223430943 n with h8 | h8
        · -- n > 9919223430943
          rcases Nat.lt_or_ge 9943770891833 n with h10 | h10
          · -- n > 9943770891833
            rcases Nat.lt_or_ge 9968379101201 n with h12 | h12
            · -- n > 9968379101201
              exact RamareSaouter2003.prime_interval_nat_ladder_c02831 n (by omega) (by omega)
            · -- n <= 9968379101201
              exact RamareSaouter2003.prime_interval_nat_ladder_c02830 n (by omega) (by omega)
          · -- n <= 9943770891833
            exact RamareSaouter2003.prime_interval_nat_ladder_c02829 n (by omega) (by omega)
        · -- n <= 9919223430943
          rcases Nat.lt_or_ge 9870310155109 n with h10 | h10
          · -- n > 9870310155109
            rcases Nat.lt_or_ge 9894736568557 n with h12 | h12
            · -- n > 9894736568557
              exact RamareSaouter2003.prime_interval_nat_ladder_c02828 n (by omega) (by omega)
            · -- n <= 9894736568557
              exact RamareSaouter2003.prime_interval_nat_ladder_c02827 n (by omega) (by omega)
          · -- n <= 9870310155109
            exact RamareSaouter2003.prime_interval_nat_ladder_c02826 n (by omega) (by omega)
  · -- n <= 9845944041601
    rcases Nat.lt_or_ge 9534604605301 n with h4 | h4
    · -- n > 9534604605301
      rcases Nat.lt_or_ge 9677057179441 n with h6 | h6
      · -- n > 9677057179441
        rcases Nat.lt_or_ge 9749079612061 n with h8 | h8
        · -- n > 9749079612061
          rcases Nat.lt_or_ge 9797392118141 n with h10 | h10
          · -- n > 9797392118141
            rcases Nat.lt_or_ge 9821638078687 n with h12 | h12
            · -- n > 9821638078687
              exact RamareSaouter2003.prime_interval_nat_ladder_c02825 n (by omega) (by omega)
            · -- n <= 9821638078687
              exact RamareSaouter2003.prime_interval_nat_ladder_c02824 n (by omega) (by omega)
          · -- n <= 9797392118141
            rcases Nat.lt_or_ge 9773206011871 n with h12 | h12
            · -- n > 9773206011871
              exact RamareSaouter2003.prime_interval_nat_ladder_c02823 n (by omega) (by omega)
            · -- n <= 9773206011871
              exact RamareSaouter2003.prime_interval_nat_ladder_c02822 n (by omega) (by omega)
        · -- n <= 9749079612061
          rcases Nat.lt_or_ge 9701005342663 n with h10 | h10
          · -- n > 9701005342663
            rcases Nat.lt_or_ge 9725012771351 n with h12 | h12
            · -- n > 9725012771351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02821 n (by omega) (by omega)
            · -- n <= 9725012771351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02820 n (by omega) (by omega)
          · -- n <= 9701005342663
            exact RamareSaouter2003.prime_interval_nat_ladder_c02819 n (by omega) (by omega)
      · -- n <= 9677057179441
        rcases Nat.lt_or_ge 9605566820653 n with h8 | h8
        · -- n > 9605566820653
          rcases Nat.lt_or_ge 9629338064201 n with h10 | h10
          · -- n > 9629338064201
            rcases Nat.lt_or_ge 9653168135207 n with h12 | h12
            · -- n > 9653168135207
              exact RamareSaouter2003.prime_interval_nat_ladder_c02818 n (by omega) (by omega)
            · -- n <= 9653168135207
              exact RamareSaouter2003.prime_interval_nat_ladder_c02817 n (by omega) (by omega)
          · -- n <= 9629338064201
            exact RamareSaouter2003.prime_interval_nat_ladder_c02816 n (by omega) (by omega)
        · -- n <= 9605566820653
          rcases Nat.lt_or_ge 9558200236069 n with h10 | h10
          · -- n > 9558200236069
            rcases Nat.lt_or_ge 9581854259633 n with h12 | h12
            · -- n > 9581854259633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02815 n (by omega) (by omega)
            · -- n <= 9581854259633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02814 n (by omega) (by omega)
          · -- n <= 9558200236069
            exact RamareSaouter2003.prime_interval_nat_ladder_c02813 n (by omega) (by omega)
    · -- n <= 9534604605301
      rcases Nat.lt_or_ge 9394249025479 n with h6 | h6
      · -- n > 9394249025479
        rcases Nat.lt_or_ge 9464166631177 n with h8 | h8
        · -- n > 9464166631177
          rcases Nat.lt_or_ge 9487587946481 n with h10 | h10
          · -- n > 9487587946481
            rcases Nat.lt_or_ge 9511067223353 n with h12 | h12
            · -- n > 9511067223353
              exact RamareSaouter2003.prime_interval_nat_ladder_c02812 n (by omega) (by omega)
            · -- n <= 9511067223353
              exact RamareSaouter2003.prime_interval_nat_ladder_c02811 n (by omega) (by omega)
          · -- n <= 9487587946481
            exact RamareSaouter2003.prime_interval_nat_ladder_c02810 n (by omega) (by omega)
        · -- n <= 9464166631177
          rcases Nat.lt_or_ge 9417497313163 n with h10 | h10
          · -- n > 9417497313163
            rcases Nat.lt_or_ge 9440803134277 n with h12 | h12
            · -- n > 9440803134277
              exact RamareSaouter2003.prime_interval_nat_ladder_c02809 n (by omega) (by omega)
            · -- n <= 9440803134277
              exact RamareSaouter2003.prime_interval_nat_ladder_c02808 n (by omega) (by omega)
          · -- n <= 9417497313163
            exact RamareSaouter2003.prime_interval_nat_ladder_c02807 n (by omega) (by omega)
      · -- n <= 9394249025479
        rcases Nat.lt_or_ge 9324847943963 n with h8 | h8
        · -- n > 9324847943963
          rcases Nat.lt_or_ge 9347924482367 n with h10 | h10
          · -- n > 9347924482367
            rcases Nat.lt_or_ge 9371058129073 n with h12 | h12
            · -- n > 9371058129073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02806 n (by omega) (by omega)
            · -- n <= 9371058129073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02805 n (by omega) (by omega)
          · -- n <= 9347924482367
            exact RamareSaouter2003.prime_interval_nat_ladder_c02804 n (by omega) (by omega)
        · -- n <= 9324847943963
          rcases Nat.lt_or_ge 9278865628801 n with h10 | h10
          · -- n > 9278865628801
            rcases Nat.lt_or_ge 9301828373029 n with h12 | h12
            · -- n > 9301828373029
              exact RamareSaouter2003.prime_interval_nat_ladder_c02803 n (by omega) (by omega)
            · -- n <= 9301828373029
              exact RamareSaouter2003.prime_interval_nat_ladder_c02802 n (by omega) (by omega)
          · -- n <= 9278865628801
            exact RamareSaouter2003.prime_interval_nat_ladder_c02801 n (by omega) (by omega)
