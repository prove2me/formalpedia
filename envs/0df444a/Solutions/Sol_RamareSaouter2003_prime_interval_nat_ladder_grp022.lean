-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T03:07:15.729911+00:00
-- url     : https://prove2.me/submissions/20b003b0-0248-4579-a9f7-05d182aa84a0

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01100

theorem solution (n : Nat)
    (hn : 114760011811 < n) (hupper : n <= 129985561751) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 122133550699 n with h2 | h2
  · -- n > 122133550699
    rcases Nat.lt_or_ge 125840919227 n with h4 | h4
    · -- n > 125840919227
      rcases Nat.lt_or_ge 127736993987 n with h6 | h6
      · -- n > 127736993987
        rcases Nat.lt_or_ge 128695818557 n with h8 | h8
        · -- n > 128695818557
          rcases Nat.lt_or_ge 129339067541 n with h10 | h10
          · -- n > 129339067541
            rcases Nat.lt_or_ge 129661907933 n with h12 | h12
            · -- n > 129661907933
              exact RamareSaouter2003.prime_interval_nat_ladder_c01100 n (by omega) (by omega)
            · -- n <= 129661907933
              exact RamareSaouter2003.prime_interval_nat_ladder_c01099 n (by omega) (by omega)
          · -- n <= 129339067541
            rcases Nat.lt_or_ge 129017038429 n with h12 | h12
            · -- n > 129017038429
              exact RamareSaouter2003.prime_interval_nat_ladder_c01098 n (by omega) (by omega)
            · -- n <= 129017038429
              exact RamareSaouter2003.prime_interval_nat_ladder_c01097 n (by omega) (by omega)
        · -- n <= 128695818557
          rcases Nat.lt_or_ge 128055798379 n with h10 | h10
          · -- n > 128055798379
            rcases Nat.lt_or_ge 128375405861 n with h12 | h12
            · -- n > 128375405861
              exact RamareSaouter2003.prime_interval_nat_ladder_c01096 n (by omega) (by omega)
            · -- n <= 128375405861
              exact RamareSaouter2003.prime_interval_nat_ladder_c01095 n (by omega) (by omega)
          · -- n <= 128055798379
            exact RamareSaouter2003.prime_interval_nat_ladder_c01094 n (by omega) (by omega)
      · -- n <= 127736993987
        rcases Nat.lt_or_ge 126785379103 n with h8 | h8
        · -- n > 126785379103
          rcases Nat.lt_or_ge 127101786367 n with h10 | h10
          · -- n > 127101786367
            rcases Nat.lt_or_ge 127418990659 n with h12 | h12
            · -- n > 127418990659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01093 n (by omega) (by omega)
            · -- n <= 127418990659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01092 n (by omega) (by omega)
          · -- n <= 127101786367
            exact RamareSaouter2003.prime_interval_nat_ladder_c01091 n (by omega) (by omega)
        · -- n <= 126785379103
          rcases Nat.lt_or_ge 126154947563 n with h10 | h10
          · -- n > 126154947563
            rcases Nat.lt_or_ge 126469766837 n with h12 | h12
            · -- n > 126469766837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01090 n (by omega) (by omega)
            · -- n <= 126469766837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01089 n (by omega) (by omega)
          · -- n <= 126154947563
            exact RamareSaouter2003.prime_interval_nat_ladder_c01088 n (by omega) (by omega)
    · -- n <= 125840919227
      rcases Nat.lt_or_ge 123973248071 n with h6 | h6
      · -- n > 123973248071
        rcases Nat.lt_or_ge 124903560319 n with h8 | h8
        · -- n > 124903560319
          rcases Nat.lt_or_ge 125215227701 n with h10 | h10
          · -- n > 125215227701
            rcases Nat.lt_or_ge 125527679911 n with h12 | h12
            · -- n > 125527679911
              exact RamareSaouter2003.prime_interval_nat_ladder_c01087 n (by omega) (by omega)
            · -- n <= 125527679911
              exact RamareSaouter2003.prime_interval_nat_ladder_c01086 n (by omega) (by omega)
          · -- n <= 125215227701
            exact RamareSaouter2003.prime_interval_nat_ladder_c01085 n (by omega) (by omega)
        · -- n <= 124903560319
          rcases Nat.lt_or_ge 124282572499 n with h10 | h10
          · -- n > 124282572499
            rcases Nat.lt_or_ge 124592675869 n with h12 | h12
            · -- n > 124592675869
              exact RamareSaouter2003.prime_interval_nat_ladder_c01084 n (by omega) (by omega)
            · -- n <= 124592675869
              exact RamareSaouter2003.prime_interval_nat_ladder_c01083 n (by omega) (by omega)
          · -- n <= 124282572499
            exact RamareSaouter2003.prime_interval_nat_ladder_c01082 n (by omega) (by omega)
      · -- n <= 123973248071
        rcases Nat.lt_or_ge 123049929269 n with h8 | h8
        · -- n > 123049929269
          rcases Nat.lt_or_ge 123356928473 n with h10 | h10
          · -- n > 123356928473
            rcases Nat.lt_or_ge 123664700717 n with h12 | h12
            · -- n > 123664700717
              exact RamareSaouter2003.prime_interval_nat_ladder_c01081 n (by omega) (by omega)
            · -- n <= 123664700717
              exact RamareSaouter2003.prime_interval_nat_ladder_c01080 n (by omega) (by omega)
          · -- n <= 123356928473
            exact RamareSaouter2003.prime_interval_nat_ladder_c01079 n (by omega) (by omega)
        · -- n <= 123049929269
          rcases Nat.lt_or_ge 122438242331 n with h10 | h10
          · -- n > 122438242331
            rcases Nat.lt_or_ge 122743701211 n with h12 | h12
            · -- n > 122743701211
              exact RamareSaouter2003.prime_interval_nat_ladder_c01078 n (by omega) (by omega)
            · -- n <= 122743701211
              exact RamareSaouter2003.prime_interval_nat_ladder_c01077 n (by omega) (by omega)
          · -- n <= 122438242331
            exact RamareSaouter2003.prime_interval_nat_ladder_c01076 n (by omega) (by omega)
  · -- n <= 122133550699
    rcases Nat.lt_or_ge 118241500501 n with h4 | h4
    · -- n > 118241500501
      rcases Nat.lt_or_ge 120022029349 n with h6 | h6
      · -- n > 120022029349
        rcases Nat.lt_or_ge 120922417841 n with h8 | h8
        · -- n > 120922417841
          rcases Nat.lt_or_ge 121526461379 n with h10 | h10
          · -- n > 121526461379
            rcases Nat.lt_or_ge 121829624353 n with h12 | h12
            · -- n > 121829624353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01075 n (by omega) (by omega)
            · -- n <= 121829624353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01074 n (by omega) (by omega)
          · -- n <= 121526461379
            rcases Nat.lt_or_ge 121224059927 n with h12 | h12
            · -- n > 121224059927
              exact RamareSaouter2003.prime_interval_nat_ladder_c01073 n (by omega) (by omega)
            · -- n <= 121224059927
              exact RamareSaouter2003.prime_interval_nat_ladder_c01072 n (by omega) (by omega)
        · -- n <= 120922417841
          rcases Nat.lt_or_ge 120321404479 n with h10 | h10
          · -- n > 120321404479
            rcases Nat.lt_or_ge 120621533327 n with h12 | h12
            · -- n > 120621533327
              exact RamareSaouter2003.prime_interval_nat_ladder_c01071 n (by omega) (by omega)
            · -- n <= 120621533327
              exact RamareSaouter2003.prime_interval_nat_ladder_c01070 n (by omega) (by omega)
          · -- n <= 120321404479
            exact RamareSaouter2003.prime_interval_nat_ladder_c01069 n (by omega) (by omega)
      · -- n <= 120022029349
        rcases Nat.lt_or_ge 119128407329 n with h8 | h8
        · -- n > 119128407329
          rcases Nat.lt_or_ge 119425532671 n with h10 | h10
          · -- n > 119425532671
            rcases Nat.lt_or_ge 119723406037 n with h12 | h12
            · -- n > 119723406037
              exact RamareSaouter2003.prime_interval_nat_ladder_c01068 n (by omega) (by omega)
            · -- n <= 119723406037
              exact RamareSaouter2003.prime_interval_nat_ladder_c01067 n (by omega) (by omega)
          · -- n <= 119425532671
            exact RamareSaouter2003.prime_interval_nat_ladder_c01066 n (by omega) (by omega)
        · -- n <= 119128407329
          rcases Nat.lt_or_ge 118536393163 n with h10 | h10
          · -- n > 118536393163
            rcases Nat.lt_or_ge 118832028113 n with h12 | h12
            · -- n > 118832028113
              exact RamareSaouter2003.prime_interval_nat_ladder_c01065 n (by omega) (by omega)
            · -- n <= 118832028113
              exact RamareSaouter2003.prime_interval_nat_ladder_c01064 n (by omega) (by omega)
          · -- n <= 118536393163
            exact RamareSaouter2003.prime_interval_nat_ladder_c01063 n (by omega) (by omega)
    · -- n <= 118241500501
      rcases Nat.lt_or_ge 116487629033 n with h6 | h6
      · -- n > 116487629033
        rcases Nat.lt_or_ge 117361257877 n with h8 | h8
        · -- n > 117361257877
          rcases Nat.lt_or_ge 117653934793 n with h10 | h10
          · -- n > 117653934793
            rcases Nat.lt_or_ge 117947348381 n with h12 | h12
            · -- n > 117947348381
              exact RamareSaouter2003.prime_interval_nat_ladder_c01062 n (by omega) (by omega)
            · -- n <= 117947348381
              exact RamareSaouter2003.prime_interval_nat_ladder_c01061 n (by omega) (by omega)
          · -- n <= 117653934793
            exact RamareSaouter2003.prime_interval_nat_ladder_c01060 n (by omega) (by omega)
        · -- n <= 117361257877
          rcases Nat.lt_or_ge 116778106957 n with h10 | h10
          · -- n > 116778106957
            rcases Nat.lt_or_ge 117069315859 n with h12 | h12
            · -- n > 117069315859
              exact RamareSaouter2003.prime_interval_nat_ladder_c01059 n (by omega) (by omega)
            · -- n <= 117069315859
              exact RamareSaouter2003.prime_interval_nat_ladder_c01058 n (by omega) (by omega)
          · -- n <= 116778106957
            exact RamareSaouter2003.prime_interval_nat_ladder_c01057 n (by omega) (by omega)
      · -- n <= 116487629033
        rcases Nat.lt_or_ge 115620563579 n with h8 | h8
        · -- n > 115620563579
          rcases Nat.lt_or_ge 115908859223 n with h10 | h10
          · -- n > 115908859223
            rcases Nat.lt_or_ge 116197880389 n with h12 | h12
            · -- n > 116197880389
              exact RamareSaouter2003.prime_interval_nat_ladder_c01056 n (by omega) (by omega)
            · -- n <= 116197880389
              exact RamareSaouter2003.prime_interval_nat_ladder_c01055 n (by omega) (by omega)
          · -- n <= 115908859223
            exact RamareSaouter2003.prime_interval_nat_ladder_c01054 n (by omega) (by omega)
        · -- n <= 115620563579
          rcases Nat.lt_or_ge 115046141713 n with h10 | h10
          · -- n > 115046141713
            rcases Nat.lt_or_ge 115332991681 n with h12 | h12
            · -- n > 115332991681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01053 n (by omega) (by omega)
            · -- n <= 115332991681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01052 n (by omega) (by omega)
          · -- n <= 115046141713
            exact RamareSaouter2003.prime_interval_nat_ladder_c01051 n (by omega) (by omega)
