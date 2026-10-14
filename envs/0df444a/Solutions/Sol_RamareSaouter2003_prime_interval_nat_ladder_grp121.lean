-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T20:08:04.960981+00:00
-- url     : https://prove2.me/submissions/43e80e7e-7016-47c2-b832-81fcb73ac3f4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06050

theorem solution (n : Nat)
    (hn : 52577951070072157 < n) (hupper : n <= 60561120261956563) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 56428513919421041 n with h2 | h2
  · -- n > 56428513919421041
    rcases Nat.lt_or_ge 58375737745647239 n with h4 | h4
    · -- n > 58375737745647239
      rcases Nat.lt_or_ge 59374392990986273 n with h6 | h6
      · -- n > 59374392990986273
        rcases Nat.lt_or_ge 59880120478234241 n with h8 | h8
        · -- n > 59880120478234241
          rcases Nat.lt_or_ge 60219644331953987 n with h10 | h10
          · -- n > 60219644331953987
            rcases Nat.lt_or_ge 60390142923918239 n with h12 | h12
            · -- n > 60390142923918239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06050 n (by omega) (by omega)
            · -- n <= 60390142923918239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06049 n (by omega) (by omega)
          · -- n <= 60219644331953987
            rcases Nat.lt_or_ge 60049656314080019 n with h12 | h12
            · -- n > 60049656314080019
              exact RamareSaouter2003.prime_interval_nat_ladder_c06048 n (by omega) (by omega)
            · -- n <= 60049656314080019
              exact RamareSaouter2003.prime_interval_nat_ladder_c06047 n (by omega) (by omega)
        · -- n <= 59880120478234241
          rcases Nat.lt_or_ge 59542496911433101 n with h10 | h10
          · -- n > 59542496911433101
            rcases Nat.lt_or_ge 59711062332382063 n with h12 | h12
            · -- n > 59711062332382063
              exact RamareSaouter2003.prime_interval_nat_ladder_c06046 n (by omega) (by omega)
            · -- n <= 59711062332382063
              exact RamareSaouter2003.prime_interval_nat_ladder_c06045 n (by omega) (by omega)
          · -- n <= 59542496911433101
            exact RamareSaouter2003.prime_interval_nat_ladder_c06044 n (by omega) (by omega)
      · -- n <= 59374392990986273
        rcases Nat.lt_or_ge 58872946302308689 n with h8 | h8
        · -- n > 58872946302308689
          rcases Nat.lt_or_ge 59039622076944661 n with h10 | h10
          · -- n > 59039622076944661
            rcases Nat.lt_or_ge 59206768533626341 n with h12 | h12
            · -- n > 59206768533626341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06043 n (by omega) (by omega)
            · -- n <= 59206768533626341
              exact RamareSaouter2003.prime_interval_nat_ladder_c06042 n (by omega) (by omega)
          · -- n <= 59039622076944661
            exact RamareSaouter2003.prime_interval_nat_ladder_c06041 n (by omega) (by omega)
        · -- n <= 58872946302308689
          rcases Nat.lt_or_ge 58541015779712357 n with h10 | h10
          · -- n > 58541015779712357
            rcases Nat.lt_or_ge 58706736286370239 n with h12 | h12
            · -- n > 58706736286370239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06040 n (by omega) (by omega)
            · -- n <= 58706736286370239
              exact RamareSaouter2003.prime_interval_nat_ladder_c06039 n (by omega) (by omega)
          · -- n <= 58541015779712357
            exact RamareSaouter2003.prime_interval_nat_ladder_c06038 n (by omega) (by omega)
    · -- n <= 58375737745647239
      rcases Nat.lt_or_ge 57393848900910941 n with h6 | h6
      · -- n > 57393848900910941
        rcases Nat.lt_or_ge 57882721151232463 n with h8 | h8
        · -- n > 57882721151232463
          rcases Nat.lt_or_ge 58046602533919211 n with h10 | h10
          · -- n > 58046602533919211
            rcases Nat.lt_or_ge 58210945729214483 n with h12 | h12
            · -- n > 58210945729214483
              exact RamareSaouter2003.prime_interval_nat_ladder_c06037 n (by omega) (by omega)
            · -- n <= 58210945729214483
              exact RamareSaouter2003.prime_interval_nat_ladder_c06036 n (by omega) (by omega)
          · -- n <= 58046602533919211
            exact RamareSaouter2003.prime_interval_nat_ladder_c06035 n (by omega) (by omega)
        · -- n <= 57882721151232463
          rcases Nat.lt_or_ge 57556345797900017 n with h10 | h10
          · -- n > 57556345797900017
            rcases Nat.lt_or_ge 57719302569553283 n with h12 | h12
            · -- n > 57719302569553283
              exact RamareSaouter2003.prime_interval_nat_ladder_c06034 n (by omega) (by omega)
            · -- n <= 57719302569553283
              exact RamareSaouter2003.prime_interval_nat_ladder_c06033 n (by omega) (by omega)
          · -- n <= 57556345797900017
            exact RamareSaouter2003.prime_interval_nat_ladder_c06032 n (by omega) (by omega)
      · -- n <= 57393848900910941
        rcases Nat.lt_or_ge 56909121478454177 n with h8 | h8
        · -- n > 56909121478454177
          rcases Nat.lt_or_ge 57070235567706079 n with h10 | h10
          · -- n > 57070235567706079
            rcases Nat.lt_or_ge 57231815185609247 n with h12 | h12
            · -- n > 57231815185609247
              exact RamareSaouter2003.prime_interval_nat_ladder_c06031 n (by omega) (by omega)
            · -- n <= 57231815185609247
              exact RamareSaouter2003.prime_interval_nat_ladder_c06030 n (by omega) (by omega)
          · -- n <= 57070235567706079
            exact RamareSaouter2003.prime_interval_nat_ladder_c06029 n (by omega) (by omega)
        · -- n <= 56909121478454177
          rcases Nat.lt_or_ge 56588276864530459 n with h10 | h10
          · -- n > 56588276864530459
            rcases Nat.lt_or_ge 56748468587268191 n with h12 | h12
            · -- n > 56748468587268191
              exact RamareSaouter2003.prime_interval_nat_ladder_c06028 n (by omega) (by omega)
            · -- n <= 56748468587268191
              exact RamareSaouter2003.prime_interval_nat_ladder_c06027 n (by omega) (by omega)
          · -- n <= 56588276864530459
            exact RamareSaouter2003.prime_interval_nat_ladder_c06026 n (by omega) (by omega)
  · -- n <= 56428513919421041
    rcases Nat.lt_or_ge 54392299010722991 n with h4 | h4
    · -- n > 54392299010722991
      rcases Nat.lt_or_ge 55322792498411287 n with h6 | h6
      · -- n > 55322792498411287
        rcases Nat.lt_or_ge 55793991486993517 n with h8 | h8
        · -- n > 55793991486993517
          rcases Nat.lt_or_ge 56110365352782479 n with h10 | h10
          · -- n > 56110365352782479
            rcases Nat.lt_or_ge 56269226393770583 n with h12 | h12
            · -- n > 56269226393770583
              exact RamareSaouter2003.prime_interval_nat_ladder_c06025 n (by omega) (by omega)
            · -- n <= 56269226393770583
              exact RamareSaouter2003.prime_interval_nat_ladder_c06024 n (by omega) (by omega)
          · -- n <= 56110365352782479
            rcases Nat.lt_or_ge 55951954053380713 n with h12 | h12
            · -- n > 55951954053380713
              exact RamareSaouter2003.prime_interval_nat_ladder_c06023 n (by omega) (by omega)
            · -- n <= 55951954053380713
              exact RamareSaouter2003.prime_interval_nat_ladder_c06022 n (by omega) (by omega)
        · -- n <= 55793991486993517
          rcases Nat.lt_or_ge 55479396413360347 n with h10 | h10
          · -- n > 55479396413360347
            rcases Nat.lt_or_ge 55636467940155787 n with h12 | h12
            · -- n > 55636467940155787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06021 n (by omega) (by omega)
            · -- n <= 55636467940155787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06020 n (by omega) (by omega)
          · -- n <= 55479396413360347
            exact RamareSaouter2003.prime_interval_nat_ladder_c06019 n (by omega) (by omega)
      · -- n <= 55322792498411287
        rcases Nat.lt_or_ge 54855586128093547 n with h8 | h8
        · -- n > 54855586128093547
          rcases Nat.lt_or_ge 55010880979776481 n with h10 | h10
          · -- n > 55010880979776481
            rcases Nat.lt_or_ge 55166608605846989 n with h12 | h12
            · -- n > 55166608605846989
              exact RamareSaouter2003.prime_interval_nat_ladder_c06018 n (by omega) (by omega)
            · -- n <= 55166608605846989
              exact RamareSaouter2003.prime_interval_nat_ladder_c06017 n (by omega) (by omega)
          · -- n <= 55010880979776481
            exact RamareSaouter2003.prime_interval_nat_ladder_c06016 n (by omega) (by omega)
        · -- n <= 54855586128093547
          rcases Nat.lt_or_ge 54546296299700999 n with h10 | h10
          · -- n > 54546296299700999
            rcases Nat.lt_or_ge 54700727833017263 n with h12 | h12
            · -- n > 54700727833017263
              exact RamareSaouter2003.prime_interval_nat_ladder_c06015 n (by omega) (by omega)
            · -- n <= 54700727833017263
              exact RamareSaouter2003.prime_interval_nat_ladder_c06014 n (by omega) (by omega)
          · -- n <= 54546296299700999
            exact RamareSaouter2003.prime_interval_nat_ladder_c06013 n (by omega) (by omega)
    · -- n <= 54392299010722991
      rcases Nat.lt_or_ge 53477414688654857 n with h6 | h6
      · -- n > 53477414688654857
        rcases Nat.lt_or_ge 53932916627179679 n with h8 | h8
        · -- n > 53932916627179679
          rcases Nat.lt_or_ge 54085601268077683 n with h10 | h10
          · -- n > 54085601268077683
            rcases Nat.lt_or_ge 54238733692130123 n with h12 | h12
            · -- n > 54238733692130123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06012 n (by omega) (by omega)
            · -- n <= 54238733692130123
              exact RamareSaouter2003.prime_interval_nat_ladder_c06011 n (by omega) (by omega)
          · -- n <= 54085601268077683
            exact RamareSaouter2003.prime_interval_nat_ladder_c06010 n (by omega) (by omega)
        · -- n <= 53932916627179679
          rcases Nat.lt_or_ge 53628821449286231 n with h10 | h10
          · -- n > 53628821449286231
            rcases Nat.lt_or_ge 53780660702174533 n with h12 | h12
            · -- n > 53780660702174533
              exact RamareSaouter2003.prime_interval_nat_ladder_c06009 n (by omega) (by omega)
            · -- n <= 53780660702174533
              exact RamareSaouter2003.prime_interval_nat_ladder_c06008 n (by omega) (by omega)
          · -- n <= 53628821449286231
            exact RamareSaouter2003.prime_interval_nat_ladder_c06007 n (by omega) (by omega)
      · -- n <= 53477414688654857
        rcases Nat.lt_or_ge 53025777360101759 n with h8 | h8
        · -- n > 53025777360101759
          rcases Nat.lt_or_ge 53175883887989293 n with h10 | h10
          · -- n > 53175883887989293
            rcases Nat.lt_or_ge 53326433977140613 n with h12 | h12
            · -- n > 53326433977140613
              exact RamareSaouter2003.prime_interval_nat_ladder_c06006 n (by omega) (by omega)
            · -- n <= 53326433977140613
              exact RamareSaouter2003.prime_interval_nat_ladder_c06005 n (by omega) (by omega)
          · -- n <= 53175883887989293
            exact RamareSaouter2003.prime_interval_nat_ladder_c06004 n (by omega) (by omega)
        · -- n <= 53025777360101759
          rcases Nat.lt_or_ge 52726796894342843 n with h10 | h10
          · -- n > 52726796894342843
            rcases Nat.lt_or_ge 52876078455825899 n with h12 | h12
            · -- n > 52876078455825899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06003 n (by omega) (by omega)
            · -- n <= 52876078455825899
              exact RamareSaouter2003.prime_interval_nat_ladder_c06002 n (by omega) (by omega)
          · -- n <= 52726796894342843
            exact RamareSaouter2003.prime_interval_nat_ladder_c06001 n (by omega) (by omega)
