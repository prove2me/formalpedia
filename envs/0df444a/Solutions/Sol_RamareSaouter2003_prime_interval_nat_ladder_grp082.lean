-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T08:57:49.121013+00:00
-- url     : https://prove2.me/submissions/498cf206-61c5-4cab-8d06-0e14efd6e29b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04100

theorem solution (n : Nat)
    (hn : 212343815514223 < n) (hupper : n <= 244566045604369) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 227886969636437 n with h2 | h2
  · -- n > 227886969636437
    rcases Nat.lt_or_ge 235746899042903 n with h4 | h4
    · -- n > 235746899042903
      rcases Nat.lt_or_ge 239775423167821 n with h6 | h6
      · -- n > 239775423167821
        rcases Nat.lt_or_ge 241816045827397 n with h8 | h8
        · -- n > 241816045827397
          rcases Nat.lt_or_ge 243187074935551 n with h10 | h10
          · -- n > 243187074935551
            rcases Nat.lt_or_ge 243875588084587 n with h12 | h12
            · -- n > 243875588084587
              exact RamareSaouter2003.prime_interval_nat_ladder_c04100 n (by omega) (by omega)
            · -- n <= 243875588084587
              exact RamareSaouter2003.prime_interval_nat_ladder_c04099 n (by omega) (by omega)
          · -- n <= 243187074935551
            rcases Nat.lt_or_ge 242500499387891 n with h12 | h12
            · -- n > 242500499387891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04098 n (by omega) (by omega)
            · -- n <= 242500499387891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04097 n (by omega) (by omega)
        · -- n <= 241816045827397
          rcases Nat.lt_or_ge 240453512835971 n with h10 | h10
          · -- n > 240453512835971
            rcases Nat.lt_or_ge 241133521719163 n with h12 | h12
            · -- n > 241133521719163
              exact RamareSaouter2003.prime_interval_nat_ladder_c04096 n (by omega) (by omega)
            · -- n <= 241133521719163
              exact RamareSaouter2003.prime_interval_nat_ladder_c04095 n (by omega) (by omega)
          · -- n <= 240453512835971
            exact RamareSaouter2003.prime_interval_nat_ladder_c04094 n (by omega) (by omega)
      · -- n <= 239775423167821
        rcases Nat.lt_or_ge 237752917898039 n with h8 | h8
        · -- n > 237752917898039
          rcases Nat.lt_or_ge 238425455027503 n with h10 | h10
          · -- n > 238425455027503
            rcases Nat.lt_or_ge 239100489676973 n with h12 | h12
            · -- n > 239100489676973
              exact RamareSaouter2003.prime_interval_nat_ladder_c04093 n (by omega) (by omega)
            · -- n <= 239100489676973
              exact RamareSaouter2003.prime_interval_nat_ladder_c04092 n (by omega) (by omega)
          · -- n <= 238425455027503
            exact RamareSaouter2003.prime_interval_nat_ladder_c04091 n (by omega) (by omega)
        · -- n <= 237752917898039
          rcases Nat.lt_or_ge 236414197513783 n with h10 | h10
          · -- n > 236414197513783
            rcases Nat.lt_or_ge 237081667691917 n with h12 | h12
            · -- n > 237081667691917
              exact RamareSaouter2003.prime_interval_nat_ladder_c04090 n (by omega) (by omega)
            · -- n <= 237081667691917
              exact RamareSaouter2003.prime_interval_nat_ladder_c04089 n (by omega) (by omega)
          · -- n <= 236414197513783
            exact RamareSaouter2003.prime_interval_nat_ladder_c04088 n (by omega) (by omega)
    · -- n <= 235746899042903
      rcases Nat.lt_or_ge 231783560624963 n with h6 | h6
      · -- n > 231783560624963
        rcases Nat.lt_or_ge 233757208136747 n with h8 | h8
        · -- n > 233757208136747
          rcases Nat.lt_or_ge 234418256146409 n with h10 | h10
          · -- n > 234418256146409
            rcases Nat.lt_or_ge 235081863456101 n with h12 | h12
            · -- n > 235081863456101
              exact RamareSaouter2003.prime_interval_nat_ladder_c04087 n (by omega) (by omega)
            · -- n <= 235081863456101
              exact RamareSaouter2003.prime_interval_nat_ladder_c04086 n (by omega) (by omega)
          · -- n <= 234418256146409
            exact RamareSaouter2003.prime_interval_nat_ladder_c04085 n (by omega) (by omega)
        · -- n <= 233757208136747
          rcases Nat.lt_or_ge 232439710523509 n with h10 | h10
          · -- n > 232439710523509
            rcases Nat.lt_or_ge 233097703685479 n with h12 | h12
            · -- n > 233097703685479
              exact RamareSaouter2003.prime_interval_nat_ladder_c04084 n (by omega) (by omega)
            · -- n <= 233097703685479
              exact RamareSaouter2003.prime_interval_nat_ladder_c04083 n (by omega) (by omega)
          · -- n <= 232439710523509
            exact RamareSaouter2003.prime_interval_nat_ladder_c04082 n (by omega) (by omega)
      · -- n <= 231783560624963
        rcases Nat.lt_or_ge 229827316229117 n with h8 | h8
        · -- n > 229827316229117
          rcases Nat.lt_or_ge 230477990707301 n with h10 | h10
          · -- n > 230477990707301
            rcases Nat.lt_or_ge 231129554234087 n with h12 | h12
            · -- n > 231129554234087
              exact RamareSaouter2003.prime_interval_nat_ladder_c04081 n (by omega) (by omega)
            · -- n <= 231129554234087
              exact RamareSaouter2003.prime_interval_nat_ladder_c04080 n (by omega) (by omega)
          · -- n <= 230477990707301
            exact RamareSaouter2003.prime_interval_nat_ladder_c04079 n (by omega) (by omega)
        · -- n <= 229827316229117
          rcases Nat.lt_or_ge 228531628529299 n with h10 | h10
          · -- n > 228531628529299
            rcases Nat.lt_or_ge 229178590680437 n with h12 | h12
            · -- n > 229178590680437
              exact RamareSaouter2003.prime_interval_nat_ladder_c04078 n (by omega) (by omega)
            · -- n <= 229178590680437
              exact RamareSaouter2003.prime_interval_nat_ladder_c04077 n (by omega) (by omega)
          · -- n <= 228531628529299
            exact RamareSaouter2003.prime_interval_nat_ladder_c04076 n (by omega) (by omega)
  · -- n <= 227886969636437
    rcases Nat.lt_or_ge 219667010417399 n with h4 | h4
    · -- n > 219667010417399
      rcases Nat.lt_or_ge 223422692907677 n with h6 | h6
      · -- n > 223422692907677
        rcases Nat.lt_or_ge 225324945735191 n with h8 | h8
        · -- n > 225324945735191
          rcases Nat.lt_or_ge 226602551704559 n with h10 | h10
          · -- n > 226602551704559
            rcases Nat.lt_or_ge 227243793490229 n with h12 | h12
            · -- n > 227243793490229
              exact RamareSaouter2003.prime_interval_nat_ladder_c04075 n (by omega) (by omega)
            · -- n <= 227243793490229
              exact RamareSaouter2003.prime_interval_nat_ladder_c04074 n (by omega) (by omega)
          · -- n <= 226602551704559
            rcases Nat.lt_or_ge 225962906514061 n with h12 | h12
            · -- n > 225962906514061
              exact RamareSaouter2003.prime_interval_nat_ladder_c04073 n (by omega) (by omega)
            · -- n <= 225962906514061
              exact RamareSaouter2003.prime_interval_nat_ladder_c04072 n (by omega) (by omega)
        · -- n <= 225324945735191
          rcases Nat.lt_or_ge 224055142737683 n with h10 | h10
          · -- n > 224055142737683
            rcases Nat.lt_or_ge 224689025716367 n with h12 | h12
            · -- n > 224689025716367
              exact RamareSaouter2003.prime_interval_nat_ladder_c04071 n (by omega) (by omega)
            · -- n <= 224689025716367
              exact RamareSaouter2003.prime_interval_nat_ladder_c04070 n (by omega) (by omega)
          · -- n <= 224055142737683
            exact RamareSaouter2003.prime_interval_nat_ladder_c04069 n (by omega) (by omega)
      · -- n <= 223422692907677
        rcases Nat.lt_or_ge 221537016554261 n with h8 | h8
        · -- n > 221537016554261
          rcases Nat.lt_or_ge 222163694041973 n with h10 | h10
          · -- n > 222163694041973
            rcases Nat.lt_or_ge 222791942302133 n with h12 | h12
            · -- n > 222791942302133
              exact RamareSaouter2003.prime_interval_nat_ladder_c04068 n (by omega) (by omega)
            · -- n <= 222791942302133
              exact RamareSaouter2003.prime_interval_nat_ladder_c04067 n (by omega) (by omega)
          · -- n <= 222163694041973
            exact RamareSaouter2003.prime_interval_nat_ladder_c04066 n (by omega) (by omega)
        · -- n <= 221537016554261
          rcases Nat.lt_or_ge 220288782269081 n with h10 | h10
          · -- n > 220288782269081
            rcases Nat.lt_or_ge 220912355029427 n with h12 | h12
            · -- n > 220912355029427
              exact RamareSaouter2003.prime_interval_nat_ladder_c04065 n (by omega) (by omega)
            · -- n <= 220912355029427
              exact RamareSaouter2003.prime_interval_nat_ladder_c04064 n (by omega) (by omega)
          · -- n <= 220288782269081
            exact RamareSaouter2003.prime_interval_nat_ladder_c04063 n (by omega) (by omega)
    · -- n <= 219667010417399
      rcases Nat.lt_or_ge 215974756465003 n with h6 | h6
      · -- n > 215974756465003
        rcases Nat.lt_or_ge 217813636386037 n with h8 | h8
        · -- n > 217813636386037
          rcases Nat.lt_or_ge 218429234412707 n with h10 | h10
          · -- n > 218429234412707
            rcases Nat.lt_or_ge 219046915330609 n with h12 | h12
            · -- n > 219046915330609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04062 n (by omega) (by omega)
            · -- n <= 219046915330609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04061 n (by omega) (by omega)
          · -- n <= 218429234412707
            exact RamareSaouter2003.prime_interval_nat_ladder_c04060 n (by omega) (by omega)
        · -- n <= 217813636386037
          rcases Nat.lt_or_ge 216586163767663 n with h10 | h10
          · -- n > 216586163767663
            rcases Nat.lt_or_ge 217199171515609 n with h12 | h12
            · -- n > 217199171515609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04059 n (by omega) (by omega)
            · -- n <= 217199171515609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04058 n (by omega) (by omega)
          · -- n <= 216586163767663
            exact RamareSaouter2003.prime_interval_nat_ladder_c04057 n (by omega) (by omega)
      · -- n <= 215974756465003
        rcases Nat.lt_or_ge 214151164475933 n with h8 | h8
        · -- n > 214151164475933
          rcases Nat.lt_or_ge 214757437492883 n with h10 | h10
          · -- n > 214757437492883
            rcases Nat.lt_or_ge 215365211963423 n with h12 | h12
            · -- n > 215365211963423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04056 n (by omega) (by omega)
            · -- n <= 215365211963423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04055 n (by omega) (by omega)
          · -- n <= 214757437492883
            exact RamareSaouter2003.prime_interval_nat_ladder_c04054 n (by omega) (by omega)
        · -- n <= 214151164475933
          rcases Nat.lt_or_ge 212944986255577 n with h10 | h10
          · -- n > 212944986255577
            rcases Nat.lt_or_ge 213547416340211 n with h12 | h12
            · -- n > 213547416340211
              exact RamareSaouter2003.prime_interval_nat_ladder_c04053 n (by omega) (by omega)
            · -- n <= 213547416340211
              exact RamareSaouter2003.prime_interval_nat_ladder_c04052 n (by omega) (by omega)
          · -- n <= 212944986255577
            exact RamareSaouter2003.prime_interval_nat_ladder_c04051 n (by omega) (by omega)
