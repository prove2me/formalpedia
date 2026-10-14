-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T01:08:05.790229+00:00
-- url     : https://prove2.me/submissions/2a0637ea-f91f-4f6b-8699-057efbf04d3f

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02950

theorem solution (n : Nat)
    (hn : 11851275819517 < n) (hupper : n <= 13410251849639) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 12606688442251 n with h2 | h2
  · -- n > 12606688442251
    rcases Nat.lt_or_ge 12986205131803 n with h4 | h4
    · -- n > 12986205131803
      rcases Nat.lt_or_ge 13180226638541 n with h6 | h6
      · -- n > 13180226638541
        rcases Nat.lt_or_ge 13278321748381 n with h8 | h8
        · -- n > 13278321748381
          rcases Nat.lt_or_ge 13344123754961 n with h10 | h10
          · -- n > 13344123754961
            rcases Nat.lt_or_ge 13377146940541 n with h12 | h12
            · -- n > 13377146940541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02950 n (by omega) (by omega)
            · -- n <= 13377146940541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02949 n (by omega) (by omega)
          · -- n <= 13344123754961
            rcases Nat.lt_or_ge 13311182091349 n with h12 | h12
            · -- n > 13311182091349
              exact RamareSaouter2003.prime_interval_nat_ladder_c02948 n (by omega) (by omega)
            · -- n <= 13311182091349
              exact RamareSaouter2003.prime_interval_nat_ladder_c02947 n (by omega) (by omega)
        · -- n <= 13278321748381
          rcases Nat.lt_or_ge 13212844221947 n with h10 | h10
          · -- n > 13212844221947
            rcases Nat.lt_or_ge 13245542525317 n with h12 | h12
            · -- n > 13245542525317
              exact RamareSaouter2003.prime_interval_nat_ladder_c02946 n (by omega) (by omega)
            · -- n <= 13245542525317
              exact RamareSaouter2003.prime_interval_nat_ladder_c02945 n (by omega) (by omega)
          · -- n <= 13212844221947
            exact RamareSaouter2003.prime_interval_nat_ladder_c02944 n (by omega) (by omega)
      · -- n <= 13180226638541
        rcases Nat.lt_or_ge 13082856217471 n with h8 | h8
        · -- n > 13082856217471
          rcases Nat.lt_or_ge 13115232834827 n with h10 | h10
          · -- n > 13115232834827
            rcases Nat.lt_or_ge 13147689575729 n with h12 | h12
            · -- n > 13147689575729
              exact RamareSaouter2003.prime_interval_nat_ladder_c02943 n (by omega) (by omega)
            · -- n <= 13147689575729
              exact RamareSaouter2003.prime_interval_nat_ladder_c02942 n (by omega) (by omega)
          · -- n <= 13115232834827
            exact RamareSaouter2003.prime_interval_nat_ladder_c02941 n (by omega) (by omega)
        · -- n <= 13082856217471
          rcases Nat.lt_or_ge 13018342563043 n with h10 | h10
          · -- n > 13018342563043
            rcases Nat.lt_or_ge 13050559526021 n with h12 | h12
            · -- n > 13050559526021
              exact RamareSaouter2003.prime_interval_nat_ladder_c02940 n (by omega) (by omega)
            · -- n <= 13050559526021
              exact RamareSaouter2003.prime_interval_nat_ladder_c02939 n (by omega) (by omega)
          · -- n <= 13018342563043
            exact RamareSaouter2003.prime_interval_nat_ladder_c02938 n (by omega) (by omega)
    · -- n <= 12986205131803
      rcases Nat.lt_or_ge 12795039747493 n with h6 | h6
      · -- n > 12795039747493
        rcases Nat.lt_or_ge 12890268066721 n with h8 | h8
        · -- n > 12890268066721
          rcases Nat.lt_or_ge 12922168079143 n with h10 | h10
          · -- n > 12922168079143
            rcases Nat.lt_or_ge 12954147035773 n with h12 | h12
            · -- n > 12954147035773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02937 n (by omega) (by omega)
            · -- n <= 12954147035773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02936 n (by omega) (by omega)
          · -- n <= 12922168079143
            exact RamareSaouter2003.prime_interval_nat_ladder_c02935 n (by omega) (by omega)
        · -- n <= 12890268066721
          rcases Nat.lt_or_ge 12826704095033 n with h10 | h10
          · -- n > 12826704095033
            rcases Nat.lt_or_ge 12858446803441 n with h12 | h12
            · -- n > 12858446803441
              exact RamareSaouter2003.prime_interval_nat_ladder_c02934 n (by omega) (by omega)
            · -- n <= 12858446803441
              exact RamareSaouter2003.prime_interval_nat_ladder_c02933 n (by omega) (by omega)
          · -- n <= 12826704095033
            exact RamareSaouter2003.prime_interval_nat_ladder_c02932 n (by omega) (by omega)
      · -- n <= 12795039747493
        rcases Nat.lt_or_ge 12700514938513 n with h8 | h8
        · -- n > 12700514938513
          rcases Nat.lt_or_ge 12731945362079 n with h10 | h10
          · -- n > 12731945362079
            rcases Nat.lt_or_ge 12763453567619 n with h12 | h12
            · -- n > 12763453567619
              exact RamareSaouter2003.prime_interval_nat_ladder_c02931 n (by omega) (by omega)
            · -- n <= 12763453567619
              exact RamareSaouter2003.prime_interval_nat_ladder_c02930 n (by omega) (by omega)
          · -- n <= 12731945362079
            exact RamareSaouter2003.prime_interval_nat_ladder_c02929 n (by omega) (by omega)
        · -- n <= 12700514938513
          rcases Nat.lt_or_ge 12637886669899 n with h10 | h10
          · -- n > 12637886669899
            rcases Nat.lt_or_ge 12669162105001 n with h12 | h12
            · -- n > 12669162105001
              exact RamareSaouter2003.prime_interval_nat_ladder_c02928 n (by omega) (by omega)
            · -- n <= 12669162105001
              exact RamareSaouter2003.prime_interval_nat_ladder_c02927 n (by omega) (by omega)
          · -- n <= 12637886669899
            exact RamareSaouter2003.prime_interval_nat_ladder_c02926 n (by omega) (by omega)
  · -- n <= 12606688442251
    rcases Nat.lt_or_ge 12208051271243 n with h4 | h4
    · -- n > 12208051271243
      rcases Nat.lt_or_ge 12390446704021 n with h6 | h6
      · -- n > 12390446704021
        rcases Nat.lt_or_ge 12482663800361 n with h8 | h8
        · -- n > 12482663800361
          rcases Nat.lt_or_ge 12544522847047 n with h10 | h10
          · -- n > 12544522847047
            rcases Nat.lt_or_ge 12575567231281 n with h12 | h12
            · -- n > 12575567231281
              exact RamareSaouter2003.prime_interval_nat_ladder_c02925 n (by omega) (by omega)
            · -- n <= 12575567231281
              exact RamareSaouter2003.prime_interval_nat_ladder_c02924 n (by omega) (by omega)
          · -- n <= 12544522847047
            rcases Nat.lt_or_ge 12513555099737 n with h12 | h12
            · -- n > 12513555099737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02923 n (by omega) (by omega)
            · -- n <= 12513555099737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02922 n (by omega) (by omega)
        · -- n <= 12482663800361
          rcases Nat.lt_or_ge 12421109790413 n with h10 | h10
          · -- n > 12421109790413
            rcases Nat.lt_or_ge 12451848759967 n with h12 | h12
            · -- n > 12451848759967
              exact RamareSaouter2003.prime_interval_nat_ladder_c02921 n (by omega) (by omega)
            · -- n <= 12451848759967
              exact RamareSaouter2003.prime_interval_nat_ladder_c02920 n (by omega) (by omega)
          · -- n <= 12421109790413
            exact RamareSaouter2003.prime_interval_nat_ladder_c02919 n (by omega) (by omega)
      · -- n <= 12390446704021
        rcases Nat.lt_or_ge 12298910871991 n with h8 | h8
        · -- n > 12298910871991
          rcases Nat.lt_or_ge 12329347431469 n with h10 | h10
          · -- n > 12329347431469
            rcases Nat.lt_or_ge 12359859313231 n with h12 | h12
            · -- n > 12359859313231
              exact RamareSaouter2003.prime_interval_nat_ladder_c02918 n (by omega) (by omega)
            · -- n <= 12359859313231
              exact RamareSaouter2003.prime_interval_nat_ladder_c02917 n (by omega) (by omega)
          · -- n <= 12329347431469
            exact RamareSaouter2003.prime_interval_nat_ladder_c02916 n (by omega) (by omega)
        · -- n <= 12298910871991
          rcases Nat.lt_or_ge 12238262977123 n with h10 | h10
          · -- n > 12238262977123
            rcases Nat.lt_or_ge 12268549449061 n with h12 | h12
            · -- n > 12268549449061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02915 n (by omega) (by omega)
            · -- n <= 12268549449061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02914 n (by omega) (by omega)
          · -- n <= 12238262977123
            exact RamareSaouter2003.prime_interval_nat_ladder_c02913 n (by omega) (by omega)
    · -- n <= 12208051271243
      rcases Nat.lt_or_ge 12028340818103 n with h6 | h6
      · -- n > 12028340818103
        rcases Nat.lt_or_ge 12117862906291 n with h8 | h8
        · -- n > 12117862906291
          rcases Nat.lt_or_ge 12147851419633 n with h10 | h10
          · -- n > 12147851419633
            rcases Nat.lt_or_ge 12177914146793 n with h12 | h12
            · -- n > 12177914146793
              exact RamareSaouter2003.prime_interval_nat_ladder_c02912 n (by omega) (by omega)
            · -- n <= 12177914146793
              exact RamareSaouter2003.prime_interval_nat_ladder_c02911 n (by omega) (by omega)
          · -- n <= 12147851419633
            exact RamareSaouter2003.prime_interval_nat_ladder_c02910 n (by omega) (by omega)
        · -- n <= 12117862906291
          rcases Nat.lt_or_ge 12058107788021 n with h10 | h10
          · -- n > 12058107788021
            rcases Nat.lt_or_ge 12087948423281 n with h12 | h12
            · -- n > 12087948423281
              exact RamareSaouter2003.prime_interval_nat_ladder_c02909 n (by omega) (by omega)
            · -- n <= 12087948423281
              exact RamareSaouter2003.prime_interval_nat_ladder_c02908 n (by omega) (by omega)
          · -- n <= 12058107788021
            exact RamareSaouter2003.prime_interval_nat_ladder_c02907 n (by omega) (by omega)
      · -- n <= 12028340818103
        rcases Nat.lt_or_ge 11939480084431 n with h8 | h8
        · -- n > 11939480084431
          rcases Nat.lt_or_ge 11969027147461 n with h10 | h10
          · -- n > 11969027147461
            rcases Nat.lt_or_ge 11998647331669 n with h12 | h12
            · -- n > 11998647331669
              exact RamareSaouter2003.prime_interval_nat_ladder_c02906 n (by omega) (by omega)
            · -- n <= 11998647331669
              exact RamareSaouter2003.prime_interval_nat_ladder_c02905 n (by omega) (by omega)
          · -- n <= 11969027147461
            exact RamareSaouter2003.prime_interval_nat_ladder_c02904 n (by omega) (by omega)
        · -- n <= 11939480084431
          rcases Nat.lt_or_ge 11880604600339 n with h10 | h10
          · -- n > 11880604600339
            rcases Nat.lt_or_ge 11910005962061 n with h12 | h12
            · -- n > 11910005962061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02903 n (by omega) (by omega)
            · -- n <= 11910005962061
              exact RamareSaouter2003.prime_interval_nat_ladder_c02902 n (by omega) (by omega)
          · -- n <= 11880604600339
            exact RamareSaouter2003.prime_interval_nat_ladder_c02901 n (by omega) (by omega)
