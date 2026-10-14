-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T10:26:50.591462+00:00
-- url     : https://prove2.me/submissions/fde65701-8b8b-4d27-91ec-e7e4a1df7c2b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07836
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07837
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07838
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07839
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07840
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07841
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07842
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07843
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07844
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07845
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07846
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07847
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07848
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07849
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07850
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07884

theorem solution (n : Nat)
    (hn : 9417226134267899261 < n) (hupper : n <= 10816557704663328019) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 10078412127782857951 n with h2 | h2
  · -- n > 10078412127782857951
    rcases Nat.lt_or_ge 10426214637193716143 n with h4 | h4
    · -- n > 10426214637193716143
      rcases Nat.lt_or_ge 10604591206485625103 n with h6 | h6
      · -- n > 10604591206485625103
        rcases Nat.lt_or_ge 10694920465423961467 n with h8 | h8
        · -- n > 10694920465423961467
          rcases Nat.lt_or_ge 10755567033568732871 n with h10 | h10
          · -- n > 10755567033568732871
            rcases Nat.lt_or_ge 10786019233464957199 n with h12 | h12
            · -- n > 10786019233464957199
              exact RamareSaouter2003.prime_interval_nat_ladder_c07884 n (by omega) (by omega)
            · -- n <= 10786019233464957199
              exact RamareSaouter2003.prime_interval_nat_ladder_c07883 n (by omega) (by omega)
          · -- n <= 10755567033568732871
            rcases Nat.lt_or_ge 10725200836061863031 n with h12 | h12
            · -- n > 10725200836061863031
              exact RamareSaouter2003.prime_interval_nat_ladder_c07882 n (by omega) (by omega)
            · -- n <= 10725200836061863031
              exact RamareSaouter2003.prime_interval_nat_ladder_c07881 n (by omega) (by omega)
        · -- n <= 10694920465423961467
          rcases Nat.lt_or_ge 10634615929353662887 n with h10 | h10
          · -- n > 10634615929353662887
            rcases Nat.lt_or_ge 10664725746308707253 n with h12 | h12
            · -- n > 10664725746308707253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07880 n (by omega) (by omega)
            · -- n <= 10664725746308707253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07879 n (by omega) (by omega)
          · -- n <= 10634615929353662887
            exact RamareSaouter2003.prime_interval_nat_ladder_c07878 n (by omega) (by omega)
      · -- n <= 10604591206485625103
        rcases Nat.lt_or_ge 10515024807358345303 n with h8 | h8
        · -- n > 10515024807358345303
          rcases Nat.lt_or_ge 10544795912676961927 n with h10 | h10
          · -- n > 10544795912676961927
            rcases Nat.lt_or_ge 10574651430053000789 n with h12 | h12
            · -- n > 10574651430053000789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07877 n (by omega) (by omega)
            · -- n <= 10574651430053000789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07876 n (by omega) (by omega)
          · -- n <= 10544795912676961927
            exact RamareSaouter2003.prime_interval_nat_ladder_c07875 n (by omega) (by omega)
        · -- n <= 10515024807358345303
          rcases Nat.lt_or_ge 10455734340833714759 n with h10 | h10
          · -- n > 10455734340833714759
            rcases Nat.lt_or_ge 10485337740597059107 n with h12 | h12
            · -- n > 10485337740597059107
              exact RamareSaouter2003.prime_interval_nat_ladder_c07874 n (by omega) (by omega)
            · -- n <= 10485337740597059107
              exact RamareSaouter2003.prime_interval_nat_ladder_c07873 n (by omega) (by omega)
          · -- n <= 10455734340833714759
            exact RamareSaouter2003.prime_interval_nat_ladder_c07872 n (by omega) (by omega)
    · -- n <= 10426214637193716143
      rcases Nat.lt_or_ge 10250838249797675683 n with h6 | h6
      · -- n > 10250838249797675683
        rcases Nat.lt_or_ge 10338154539722143333 n with h8 | h8
        · -- n > 10338154539722143333
          rcases Nat.lt_or_ge 10367425028882972009 n with h10 | h10
          · -- n > 10367425028882972009
            rcases Nat.lt_or_ge 10396778200579565549 n with h12 | h12
            · -- n > 10396778200579565549
              exact RamareSaouter2003.prime_interval_nat_ladder_c07871 n (by omega) (by omega)
            · -- n <= 10396778200579565549
              exact RamareSaouter2003.prime_interval_nat_ladder_c07870 n (by omega) (by omega)
          · -- n <= 10367425028882972009
            exact RamareSaouter2003.prime_interval_nat_ladder_c07869 n (by omega) (by omega)
        · -- n <= 10338154539722143333
          rcases Nat.lt_or_ge 10279861437738481471 n with h10 | h10
          · -- n > 10279861437738481471
            rcases Nat.lt_or_ge 10308966719455711147 n with h12 | h12
            · -- n > 10308966719455711147
              exact RamareSaouter2003.prime_interval_nat_ladder_c07868 n (by omega) (by omega)
            · -- n <= 10308966719455711147
              exact RamareSaouter2003.prime_interval_nat_ladder_c07867 n (by omega) (by omega)
          · -- n <= 10279861437738481471
            exact RamareSaouter2003.prime_interval_nat_ladder_c07866 n (by omega) (by omega)
      · -- n <= 10250838249797675683
        rcases Nat.lt_or_ge 10164259877957841529 n with h8 | h8
        · -- n > 10164259877957841529
          rcases Nat.lt_or_ge 10193037876541546549 n with h10 | h10
          · -- n > 10193037876541546549
            rcases Nat.lt_or_ge 10221897013757705681 n with h12 | h12
            · -- n > 10221897013757705681
              exact RamareSaouter2003.prime_interval_nat_ladder_c07865 n (by omega) (by omega)
            · -- n <= 10221897013757705681
              exact RamareSaouter2003.prime_interval_nat_ladder_c07864 n (by omega) (by omega)
          · -- n <= 10193037876541546549
            exact RamareSaouter2003.prime_interval_nat_ladder_c07863 n (by omega) (by omega)
        · -- n <= 10164259877957841529
          rcases Nat.lt_or_ge 10106947203775341211 n with h10 | h10
          · -- n > 10106947203775341211
            rcases Nat.lt_or_ge 10135563025155574049 n with h12 | h12
            · -- n > 10135563025155574049
              exact RamareSaouter2003.prime_interval_nat_ladder_c07862 n (by omega) (by omega)
            · -- n <= 10135563025155574049
              exact RamareSaouter2003.prime_interval_nat_ladder_c07861 n (by omega) (by omega)
          · -- n <= 10106947203775341211
            exact RamareSaouter2003.prime_interval_nat_ladder_c07860 n (by omega) (by omega)
  · -- n <= 10078412127782857951
    rcases Nat.lt_or_ge 9742211642193383989 n with h4 | h4
    · -- n > 9742211642193383989
      rcases Nat.lt_or_ge 9908885839438158383 n with h6 | h6
      · -- n > 9908885839438158383
        rcases Nat.lt_or_ge 9993289498940636593 n with h8 | h8
        · -- n > 9993289498940636593
          rcases Nat.lt_or_ge 10021583534396687047 n with h10 | h10
          · -- n > 10021583534396687047
            rcases Nat.lt_or_ge 10049957645011826197 n with h12 | h12
            · -- n > 10049957645011826197
              exact RamareSaouter2003.prime_interval_nat_ladder_c07859 n (by omega) (by omega)
            · -- n <= 10049957645011826197
              exact RamareSaouter2003.prime_interval_nat_ladder_c07858 n (by omega) (by omega)
          · -- n <= 10021583534396687047
            exact RamareSaouter2003.prime_interval_nat_ladder_c07857 n (by omega) (by omega)
        · -- n <= 9993289498940636593
          rcases Nat.lt_or_ge 9936940898967072967 n with h10 | h10
          · -- n > 9936940898967072967
            rcases Nat.lt_or_ge 9965075425666732559 n with h12 | h12
            · -- n > 9965075425666732559
              exact RamareSaouter2003.prime_interval_nat_ladder_c07856 n (by omega) (by omega)
            · -- n <= 9965075425666732559
              exact RamareSaouter2003.prime_interval_nat_ladder_c07855 n (by omega) (by omega)
          · -- n <= 9936940898967072967
            exact RamareSaouter2003.prime_interval_nat_ladder_c07854 n (by omega) (by omega)
      · -- n <= 9908885839438158383
        rcases Nat.lt_or_ge 9825194949081652087 n with h8 | h8
        · -- n > 9825194949081652087
          rcases Nat.lt_or_ge 9853013082022174451 n with h10 | h10
          · -- n > 9853013082022174451
            rcases Nat.lt_or_ge 9880909983740555129 n with h12 | h12
            · -- n > 9880909983740555129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07853 n (by omega) (by omega)
            · -- n <= 9880909983740555129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07852 n (by omega) (by omega)
          · -- n <= 9853013082022174451
            exact RamareSaouter2003.prime_interval_nat_ladder_c07851 n (by omega) (by omega)
        · -- n <= 9825194949081652087
          rcases Nat.lt_or_ge 9769794170465605253 n with h10 | h10
          · -- n > 9769794170465605253
            rcases Nat.lt_or_ge 9797455417631539201 n with h12 | h12
            · -- n > 9797455417631539201
              exact RamareSaouter2003.prime_interval_nat_ladder_c07850 n (by omega) (by omega)
            · -- n <= 9797455417631539201
              exact RamareSaouter2003.prime_interval_nat_ladder_c07849 n (by omega) (by omega)
          · -- n <= 9769794170465605253
            exact RamareSaouter2003.prime_interval_nat_ladder_c07848 n (by omega) (by omega)
    · -- n <= 9742211642193383989
      rcases Nat.lt_or_ge 9578340515648631959 n with h6 | h6
      · -- n > 9578340515648631959
        rcases Nat.lt_or_ge 9659928550671952187 n with h8 | h8
        · -- n > 9659928550671952187
          rcases Nat.lt_or_ge 9687278743667192659 n with h10 | h10
          · -- n > 9687278743667192659
            rcases Nat.lt_or_ge 9714706392347152909 n with h12 | h12
            · -- n > 9714706392347152909
              exact RamareSaouter2003.prime_interval_nat_ladder_c07847 n (by omega) (by omega)
            · -- n <= 9714706392347152909
              exact RamareSaouter2003.prime_interval_nat_ladder_c07846 n (by omega) (by omega)
          · -- n <= 9687278743667192659
            exact RamareSaouter2003.prime_interval_nat_ladder_c07845 n (by omega) (by omega)
        · -- n <= 9659928550671952187
          rcases Nat.lt_or_ge 9605459727439632701 n with h10 | h10
          · -- n > 9605459727439632701
            rcases Nat.lt_or_ge 9632655724184633911 n with h12 | h12
            · -- n > 9632655724184633911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07844 n (by omega) (by omega)
            · -- n <= 9632655724184633911
              exact RamareSaouter2003.prime_interval_nat_ladder_c07843 n (by omega) (by omega)
          · -- n <= 9605459727439632701
            exact RamareSaouter2003.prime_interval_nat_ladder_c07842 n (by omega) (by omega)
      · -- n <= 9578340515648631959
        rcases Nat.lt_or_ge 9497441892117124613 n with h8 | h8
        · -- n > 9497441892117124613
          rcases Nat.lt_or_ge 9524331988797121787 n with h10 | h10
          · -- n > 9524331988797121787
            rcases Nat.lt_or_ge 9551298031738019203 n with h12 | h12
            · -- n > 9551298031738019203
              exact RamareSaouter2003.prime_interval_nat_ladder_c07841 n (by omega) (by omega)
            · -- n <= 9551298031738019203
              exact RamareSaouter2003.prime_interval_nat_ladder_c07840 n (by omega) (by omega)
          · -- n <= 9524331988797121787
            exact RamareSaouter2003.prime_interval_nat_ladder_c07839 n (by omega) (by omega)
        · -- n <= 9497441892117124613
          rcases Nat.lt_or_ge 9443889190029117899 n with h10 | h10
          · -- n > 9443889190029117899
            rcases Nat.lt_or_ge 9470627734536867127 n with h12 | h12
            · -- n > 9470627734536867127
              exact RamareSaouter2003.prime_interval_nat_ladder_c07838 n (by omega) (by omega)
            · -- n <= 9470627734536867127
              exact RamareSaouter2003.prime_interval_nat_ladder_c07837 n (by omega) (by omega)
          · -- n <= 9443889190029117899
            exact RamareSaouter2003.prime_interval_nat_ladder_c07836 n (by omega) (by omega)
