-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T14:15:17.377404+00:00
-- url     : https://prove2.me/submissions/ceb6f0e5-e287-4fa5-88f7-d24f03e9aca8

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05050

theorem solution (n : Nat)
    (hn : 3112164993040603 < n) (hupper : n <= 3584629562138893) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3340060007181179 n with h2 | h2
  · -- n > 3340060007181179
    rcases Nat.lt_or_ge 3455312018370721 n with h4 | h4
    · -- n > 3455312018370721
      rcases Nat.lt_or_ge 3514405686835181 n with h6 | h6
      · -- n > 3514405686835181
        rcases Nat.lt_or_ge 3544333954482221 n with h8 | h8
        · -- n > 3544333954482221
          rcases Nat.lt_or_ge 3564425163626009 n with h10 | h10
          · -- n > 3564425163626009
            rcases Nat.lt_or_ge 3574511430375959 n with h12 | h12
            · -- n > 3574511430375959
              exact RamareSaouter2003.prime_interval_nat_ladder_c05050 n (by omega) (by omega)
            · -- n <= 3574511430375959
              exact RamareSaouter2003.prime_interval_nat_ladder_c05049 n (by omega) (by omega)
          · -- n <= 3564425163626009
            rcases Nat.lt_or_ge 3554368410087091 n with h12 | h12
            · -- n > 3554368410087091
              exact RamareSaouter2003.prime_interval_nat_ladder_c05048 n (by omega) (by omega)
            · -- n <= 3554368410087091
              exact RamareSaouter2003.prime_interval_nat_ladder_c05047 n (by omega) (by omega)
        · -- n <= 3544333954482221
          rcases Nat.lt_or_ge 3524349269516627 n with h10 | h10
          · -- n > 3524349269516627
            rcases Nat.lt_or_ge 3534327713922389 n with h12 | h12
            · -- n > 3534327713922389
              exact RamareSaouter2003.prime_interval_nat_ladder_c05046 n (by omega) (by omega)
            · -- n <= 3534327713922389
              exact RamareSaouter2003.prime_interval_nat_ladder_c05045 n (by omega) (by omega)
          · -- n <= 3524349269516627
            exact RamareSaouter2003.prime_interval_nat_ladder_c05044 n (by omega) (by omega)
      · -- n <= 3514405686835181
        rcases Nat.lt_or_ge 3484734180442069 n with h8 | h8
        · -- n > 3484734180442069
          rcases Nat.lt_or_ge 3494597660736629 n with h10 | h10
          · -- n > 3494597660736629
            rcases Nat.lt_or_ge 3504485261973739 n with h12 | h12
            · -- n > 3504485261973739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05043 n (by omega) (by omega)
            · -- n <= 3504485261973739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05042 n (by omega) (by omega)
          · -- n <= 3494597660736629
            exact RamareSaouter2003.prime_interval_nat_ladder_c05041 n (by omega) (by omega)
        · -- n <= 3484734180442069
          rcases Nat.lt_or_ge 3465094834998983 n with h10 | h10
          · -- n > 3465094834998983
            rcases Nat.lt_or_ge 3474895716108361 n with h12 | h12
            · -- n > 3474895716108361
              exact RamareSaouter2003.prime_interval_nat_ladder_c05040 n (by omega) (by omega)
            · -- n <= 3474895716108361
              exact RamareSaouter2003.prime_interval_nat_ladder_c05039 n (by omega) (by omega)
          · -- n <= 3465094834998983
            exact RamareSaouter2003.prime_interval_nat_ladder_c05038 n (by omega) (by omega)
    · -- n <= 3455312018370721
      rcases Nat.lt_or_ge 3397198018424809 n with h6 | h6
      · -- n > 3397198018424809
        rcases Nat.lt_or_ge 3426131543043301 n with h8 | h8
        · -- n > 3426131543043301
          rcases Nat.lt_or_ge 3435831488194333 n with h10 | h10
          · -- n > 3435831488194333
            rcases Nat.lt_or_ge 3445557475471093 n with h12 | h12
            · -- n > 3445557475471093
              exact RamareSaouter2003.prime_interval_nat_ladder_c05037 n (by omega) (by omega)
            · -- n <= 3445557475471093
              exact RamareSaouter2003.prime_interval_nat_ladder_c05036 n (by omega) (by omega)
          · -- n <= 3435831488194333
            exact RamareSaouter2003.prime_interval_nat_ladder_c05035 n (by omega) (by omega)
        · -- n <= 3426131543043301
          rcases Nat.lt_or_ge 3406816207994909 n with h10 | h10
          · -- n > 3406816207994909
            rcases Nat.lt_or_ge 3416460738023239 n with h12 | h12
            · -- n > 3416460738023239
              exact RamareSaouter2003.prime_interval_nat_ladder_c05034 n (by omega) (by omega)
            · -- n <= 3416460738023239
              exact RamareSaouter2003.prime_interval_nat_ladder_c05033 n (by omega) (by omega)
          · -- n <= 3406816207994909
            exact RamareSaouter2003.prime_interval_nat_ladder_c05032 n (by omega) (by omega)
      · -- n <= 3397198018424809
        rcases Nat.lt_or_ge 3368508485949041 n with h8 | h8
        · -- n > 3368508485949041
          rcases Nat.lt_or_ge 3378045434854487 n with h10 | h10
          · -- n > 3378045434854487
            rcases Nat.lt_or_ge 3387609721239923 n with h12 | h12
            · -- n > 3387609721239923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05031 n (by omega) (by omega)
            · -- n <= 3387609721239923
              exact RamareSaouter2003.prime_interval_nat_ladder_c05030 n (by omega) (by omega)
          · -- n <= 3378045434854487
            exact RamareSaouter2003.prime_interval_nat_ladder_c05029 n (by omega) (by omega)
        · -- n <= 3368508485949041
          rcases Nat.lt_or_ge 3349515539127787 n with h10 | h10
          · -- n > 3349515539127787
            rcases Nat.lt_or_ge 3358998693650947 n with h12 | h12
            · -- n > 3358998693650947
              exact RamareSaouter2003.prime_interval_nat_ladder_c05028 n (by omega) (by omega)
            · -- n <= 3358998693650947
              exact RamareSaouter2003.prime_interval_nat_ladder_c05027 n (by omega) (by omega)
          · -- n <= 3349515539127787
            exact RamareSaouter2003.prime_interval_nat_ladder_c05026 n (by omega) (by omega)
  · -- n <= 3340060007181179
    rcases Nat.lt_or_ge 3219551679476299 n with h4 | h4
    · -- n > 3219551679476299
      rcases Nat.lt_or_ge 3274617111391277 n with h6 | h6
      · -- n > 3274617111391277
        rcases Nat.lt_or_ge 3302506467141121 n with h8 | h8
        · -- n > 3302506467141121
          rcases Nat.lt_or_ge 3321228227532079 n with h10 | h10
          · -- n > 3321228227532079
            rcases Nat.lt_or_ge 3330630999076697 n with h12 | h12
            · -- n > 3330630999076697
              exact RamareSaouter2003.prime_interval_nat_ladder_c05025 n (by omega) (by omega)
            · -- n <= 3330630999076697
              exact RamareSaouter2003.prime_interval_nat_ladder_c05024 n (by omega) (by omega)
          · -- n <= 3321228227532079
            rcases Nat.lt_or_ge 3311856243277633 n with h12 | h12
            · -- n > 3311856243277633
              exact RamareSaouter2003.prime_interval_nat_ladder_c05023 n (by omega) (by omega)
            · -- n <= 3311856243277633
              exact RamareSaouter2003.prime_interval_nat_ladder_c05022 n (by omega) (by omega)
        · -- n <= 3302506467141121
          rcases Nat.lt_or_ge 3283887360346949 n with h10 | h10
          · -- n > 3283887360346949
            rcases Nat.lt_or_ge 3293182988520587 n with h12 | h12
            · -- n > 3293182988520587
              exact RamareSaouter2003.prime_interval_nat_ladder_c05021 n (by omega) (by omega)
            · -- n <= 3293182988520587
              exact RamareSaouter2003.prime_interval_nat_ladder_c05020 n (by omega) (by omega)
          · -- n <= 3283887360346949
            exact RamareSaouter2003.prime_interval_nat_ladder_c05019 n (by omega) (by omega)
      · -- n <= 3274617111391277
        rcases Nat.lt_or_ge 3246972755879221 n with h8 | h8
        · -- n > 3246972755879221
          rcases Nat.lt_or_ge 3256163527256249 n with h10 | h10
          · -- n > 3256163527256249
            rcases Nat.lt_or_ge 3265379746272883 n with h12 | h12
            · -- n > 3265379746272883
              exact RamareSaouter2003.prime_interval_nat_ladder_c05018 n (by omega) (by omega)
            · -- n <= 3265379746272883
              exact RamareSaouter2003.prime_interval_nat_ladder_c05017 n (by omega) (by omega)
          · -- n <= 3256163527256249
            exact RamareSaouter2003.prime_interval_nat_ladder_c05016 n (by omega) (by omega)
        · -- n <= 3246972755879221
          rcases Nat.lt_or_ge 3228664609438531 n with h10 | h10
          · -- n > 3228664609438531
            rcases Nat.lt_or_ge 3237805555275689 n with h12 | h12
            · -- n > 3237805555275689
              exact RamareSaouter2003.prime_interval_nat_ladder_c05015 n (by omega) (by omega)
            · -- n <= 3237805555275689
              exact RamareSaouter2003.prime_interval_nat_ladder_c05014 n (by omega) (by omega)
          · -- n <= 3228664609438531
            exact RamareSaouter2003.prime_interval_nat_ladder_c05013 n (by omega) (by omega)
    · -- n <= 3219551679476299
      rcases Nat.lt_or_ge 3165402118287133 n with h6 | h6
      · -- n > 3165402118287133
        rcases Nat.lt_or_ge 3192361694343769 n with h8 | h8
        · -- n > 3192361694343769
          rcases Nat.lt_or_ge 3201400217261761 n with h10 | h10
          · -- n > 3201400217261761
            rcases Nat.lt_or_ge 3210463415521493 n with h12 | h12
            · -- n > 3210463415521493
              exact RamareSaouter2003.prime_interval_nat_ladder_c05012 n (by omega) (by omega)
            · -- n <= 3210463415521493
              exact RamareSaouter2003.prime_interval_nat_ladder_c05011 n (by omega) (by omega)
          · -- n <= 3201400217261761
            exact RamareSaouter2003.prime_interval_nat_ladder_c05010 n (by omega) (by omega)
        · -- n <= 3192361694343769
          rcases Nat.lt_or_ge 3174362078250859 n with h10 | h10
          · -- n > 3174362078250859
            rcases Nat.lt_or_ge 3183349150410151 n with h12 | h12
            · -- n > 3183349150410151
              exact RamareSaouter2003.prime_interval_nat_ladder_c05009 n (by omega) (by omega)
            · -- n <= 3183349150410151
              exact RamareSaouter2003.prime_interval_nat_ladder_c05008 n (by omega) (by omega)
          · -- n <= 3174362078250859
            exact RamareSaouter2003.prime_interval_nat_ladder_c05007 n (by omega) (by omega)
      · -- n <= 3165402118287133
        rcases Nat.lt_or_ge 3138670813359293 n with h8 | h8
        · -- n > 3138670813359293
          rcases Nat.lt_or_ge 3147556985497789 n with h10 | h10
          · -- n > 3147556985497789
            rcases Nat.lt_or_ge 3156466841451169 n with h12 | h12
            · -- n > 3156466841451169
              exact RamareSaouter2003.prime_interval_nat_ladder_c05006 n (by omega) (by omega)
            · -- n <= 3156466841451169
              exact RamareSaouter2003.prime_interval_nat_ladder_c05005 n (by omega) (by omega)
          · -- n <= 3147556985497789
            exact RamareSaouter2003.prime_interval_nat_ladder_c05004 n (by omega) (by omega)
        · -- n <= 3138670813359293
          rcases Nat.lt_or_ge 3120976377035213 n with h10 | h10
          · -- n > 3120976377035213
            rcases Nat.lt_or_ge 3129812312147687 n with h12 | h12
            · -- n > 3129812312147687
              exact RamareSaouter2003.prime_interval_nat_ladder_c05003 n (by omega) (by omega)
            · -- n <= 3129812312147687
              exact RamareSaouter2003.prime_interval_nat_ladder_c05002 n (by omega) (by omega)
          · -- n <= 3120976377035213
            exact RamareSaouter2003.prime_interval_nat_ladder_c05001 n (by omega) (by omega)
