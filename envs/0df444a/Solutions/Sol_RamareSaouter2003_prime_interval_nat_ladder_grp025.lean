-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T05:00:22.098187+00:00
-- url     : https://prove2.me/submissions/54100468-fbe0-4dc8-abe6-7058176607b5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01250

theorem solution (n : Nat)
    (hn : 166837303537 < n) (hupper : n <= 189054413519) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 177595557169 n with h2 | h2
  · -- n > 177595557169
    rcases Nat.lt_or_ge 183005605963 n with h4 | h4
    · -- n > 183005605963
      rcases Nat.lt_or_ge 185772705571 n with h6 | h6
      · -- n > 185772705571
        rcases Nat.lt_or_ge 187172052959 n with h8 | h8
        · -- n > 187172052959
          rcases Nat.lt_or_ge 188110856819 n with h10 | h10
          · -- n > 188110856819
            rcases Nat.lt_or_ge 188582039609 n with h12 | h12
            · -- n > 188582039609
              exact RamareSaouter2003.prime_interval_nat_ladder_c01250 n (by omega) (by omega)
            · -- n <= 188582039609
              exact RamareSaouter2003.prime_interval_nat_ladder_c01249 n (by omega) (by omega)
          · -- n <= 188110856819
            rcases Nat.lt_or_ge 187640862301 n with h12 | h12
            · -- n > 187640862301
              exact RamareSaouter2003.prime_interval_nat_ladder_c01248 n (by omega) (by omega)
            · -- n <= 187640862301
              exact RamareSaouter2003.prime_interval_nat_ladder_c01247 n (by omega) (by omega)
        · -- n <= 187172052959
          rcases Nat.lt_or_ge 186237977557 n with h10 | h10
          · -- n > 186237977557
            rcases Nat.lt_or_ge 186704425697 n with h12 | h12
            · -- n > 186704425697
              exact RamareSaouter2003.prime_interval_nat_ladder_c01246 n (by omega) (by omega)
            · -- n <= 186704425697
              exact RamareSaouter2003.prime_interval_nat_ladder_c01245 n (by omega) (by omega)
          · -- n <= 186237977557
            exact RamareSaouter2003.prime_interval_nat_ladder_c01244 n (by omega) (by omega)
      · -- n <= 185772705571
        rcases Nat.lt_or_ge 184383916693 n with h8 | h8
        · -- n > 184383916693
          rcases Nat.lt_or_ge 184845678161 n with h10 | h10
          · -- n > 184845678161
            rcases Nat.lt_or_ge 185308606823 n with h12 | h12
            · -- n > 185308606823
              exact RamareSaouter2003.prime_interval_nat_ladder_c01243 n (by omega) (by omega)
            · -- n <= 185308606823
              exact RamareSaouter2003.prime_interval_nat_ladder_c01242 n (by omega) (by omega)
          · -- n <= 184845678161
            exact RamareSaouter2003.prime_interval_nat_ladder_c01241 n (by omega) (by omega)
        · -- n <= 184383916693
          rcases Nat.lt_or_ge 183463883633 n with h10 | h10
          · -- n > 183463883633
            rcases Nat.lt_or_ge 183923319473 n with h12 | h12
            · -- n > 183923319473
              exact RamareSaouter2003.prime_interval_nat_ladder_c01240 n (by omega) (by omega)
            · -- n <= 183923319473
              exact RamareSaouter2003.prime_interval_nat_ladder_c01239 n (by omega) (by omega)
          · -- n <= 183463883633
            exact RamareSaouter2003.prime_interval_nat_ladder_c01238 n (by omega) (by omega)
    · -- n <= 183005605963
      rcases Nat.lt_or_ge 180280100059 n with h6 | h6
      · -- n > 180280100059
        rcases Nat.lt_or_ge 181637693473 n with h8 | h8
        · -- n > 181637693473
          rcases Nat.lt_or_ge 182092513871 n with h10 | h10
          · -- n > 182092513871
            rcases Nat.lt_or_ge 182548483757 n with h12 | h12
            · -- n > 182548483757
              exact RamareSaouter2003.prime_interval_nat_ladder_c01237 n (by omega) (by omega)
            · -- n <= 182548483757
              exact RamareSaouter2003.prime_interval_nat_ladder_c01236 n (by omega) (by omega)
          · -- n <= 182092513871
            exact RamareSaouter2003.prime_interval_nat_ladder_c01235 n (by omega) (by omega)
        · -- n <= 181637693473
          rcases Nat.lt_or_ge 180731489473 n with h10 | h10
          · -- n > 180731489473
            rcases Nat.lt_or_ge 181184019659 n with h12 | h12
            · -- n > 181184019659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01234 n (by omega) (by omega)
            · -- n <= 181184019659
              exact RamareSaouter2003.prime_interval_nat_ladder_c01233 n (by omega) (by omega)
          · -- n <= 180731489473
            exact RamareSaouter2003.prime_interval_nat_ladder_c01232 n (by omega) (by omega)
      · -- n <= 180280100059
        rcases Nat.lt_or_ge 178932747281 n with h8 | h8
        · -- n > 178932747281
          rcases Nat.lt_or_ge 179380731889 n with h10 | h10
          · -- n > 179380731889
            rcases Nat.lt_or_ge 179829848537 n with h12 | h12
            · -- n > 179829848537
              exact RamareSaouter2003.prime_interval_nat_ladder_c01231 n (by omega) (by omega)
            · -- n <= 179829848537
              exact RamareSaouter2003.prime_interval_nat_ladder_c01230 n (by omega) (by omega)
          · -- n <= 179380731889
            exact RamareSaouter2003.prime_interval_nat_ladder_c01229 n (by omega) (by omega)
        · -- n <= 178932747281
          rcases Nat.lt_or_ge 178040162827 n with h10 | h10
          · -- n > 178040162827
            rcases Nat.lt_or_ge 178485891959 n with h12 | h12
            · -- n > 178485891959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01228 n (by omega) (by omega)
            · -- n <= 178485891959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01227 n (by omega) (by omega)
          · -- n <= 178040162827
            exact RamareSaouter2003.prime_interval_nat_ladder_c01226 n (by omega) (by omega)
  · -- n <= 177595557169
    rcases Nat.lt_or_ge 171916626943 n with h4 | h4
    · -- n > 171916626943
      rcases Nat.lt_or_ge 174514535101 n with h6 | h6
      · -- n > 174514535101
        rcases Nat.lt_or_ge 175828312103 n with h8 | h8
        · -- n > 175828312103
          rcases Nat.lt_or_ge 176709704861 n with h10 | h10
          · -- n > 176709704861
            rcases Nat.lt_or_ge 177152072171 n with h12 | h12
            · -- n > 177152072171
              exact RamareSaouter2003.prime_interval_nat_ladder_c01225 n (by omega) (by omega)
            · -- n <= 177152072171
              exact RamareSaouter2003.prime_interval_nat_ladder_c01224 n (by omega) (by omega)
          · -- n <= 176709704861
            rcases Nat.lt_or_ge 176268452461 n with h12 | h12
            · -- n > 176268452461
              exact RamareSaouter2003.prime_interval_nat_ladder_c01223 n (by omega) (by omega)
            · -- n <= 176268452461
              exact RamareSaouter2003.prime_interval_nat_ladder_c01222 n (by omega) (by omega)
        · -- n <= 175828312103
          rcases Nat.lt_or_ge 174951356243 n with h10 | h10
          · -- n > 174951356243
            rcases Nat.lt_or_ge 175389280919 n with h12 | h12
            · -- n > 175389280919
              exact RamareSaouter2003.prime_interval_nat_ladder_c01221 n (by omega) (by omega)
            · -- n <= 175389280919
              exact RamareSaouter2003.prime_interval_nat_ladder_c01220 n (by omega) (by omega)
          · -- n <= 174951356243
            exact RamareSaouter2003.prime_interval_nat_ladder_c01219 n (by omega) (by omega)
      · -- n <= 174514535101
        rcases Nat.lt_or_ge 173210665073 n with h8 | h8
        · -- n > 173210665073
          rcases Nat.lt_or_ge 173644192291 n with h10 | h10
          · -- n > 173644192291
            rcases Nat.lt_or_ge 174078814727 n with h12 | h12
            · -- n > 174078814727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01218 n (by omega) (by omega)
            · -- n <= 174078814727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01217 n (by omega) (by omega)
          · -- n <= 173644192291
            exact RamareSaouter2003.prime_interval_nat_ladder_c01216 n (by omega) (by omega)
        · -- n <= 173210665073
          rcases Nat.lt_or_ge 172346885209 n with h10 | h10
          · -- n > 172346885209
            rcases Nat.lt_or_ge 172778230351 n with h12 | h12
            · -- n > 172778230351
              exact RamareSaouter2003.prime_interval_nat_ladder_c01215 n (by omega) (by omega)
            · -- n <= 172778230351
              exact RamareSaouter2003.prime_interval_nat_ladder_c01214 n (by omega) (by omega)
          · -- n <= 172346885209
            exact RamareSaouter2003.prime_interval_nat_ladder_c01213 n (by omega) (by omega)
    · -- n <= 171916626943
      rcases Nat.lt_or_ge 169357746853 n with h6 | h6
      · -- n > 169357746853
        rcases Nat.lt_or_ge 170632345537 n with h8 | h8
        · -- n > 170632345537
          rcases Nat.lt_or_ge 171059359843 n with h10 | h10
          · -- n > 171059359843
            rcases Nat.lt_or_ge 171487452709 n with h12 | h12
            · -- n > 171487452709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01212 n (by omega) (by omega)
            · -- n <= 171487452709
              exact RamareSaouter2003.prime_interval_nat_ladder_c01211 n (by omega) (by omega)
          · -- n <= 171059359843
            exact RamareSaouter2003.prime_interval_nat_ladder_c01210 n (by omega) (by omega)
        · -- n <= 170632345537
          rcases Nat.lt_or_ge 169781541751 n with h10 | h10
          · -- n > 169781541751
            rcases Nat.lt_or_ge 170206407089 n with h12 | h12
            · -- n > 170206407089
              exact RamareSaouter2003.prime_interval_nat_ladder_c01209 n (by omega) (by omega)
            · -- n <= 170206407089
              exact RamareSaouter2003.prime_interval_nat_ladder_c01208 n (by omega) (by omega)
          · -- n <= 169781541751
            exact RamareSaouter2003.prime_interval_nat_ladder_c01207 n (by omega) (by omega)
      · -- n <= 169357746853
        rcases Nat.lt_or_ge 168092757311 n with h8 | h8
        · -- n > 168092757311
          rcases Nat.lt_or_ge 168513357391 n with h10 | h10
          · -- n > 168513357391
            rcases Nat.lt_or_ge 168935019607 n with h12 | h12
            · -- n > 168935019607
              exact RamareSaouter2003.prime_interval_nat_ladder_c01206 n (by omega) (by omega)
            · -- n <= 168935019607
              exact RamareSaouter2003.prime_interval_nat_ladder_c01205 n (by omega) (by omega)
          · -- n <= 168513357391
            exact RamareSaouter2003.prime_interval_nat_ladder_c01204 n (by omega) (by omega)
        · -- n <= 168092757311
          rcases Nat.lt_or_ge 167254733057 n with h10 | h10
          · -- n > 167254733057
            rcases Nat.lt_or_ge 167673216761 n with h12 | h12
            · -- n > 167673216761
              exact RamareSaouter2003.prime_interval_nat_ladder_c01203 n (by omega) (by omega)
            · -- n <= 167673216761
              exact RamareSaouter2003.prime_interval_nat_ladder_c01202 n (by omega) (by omega)
          · -- n <= 167254733057
            exact RamareSaouter2003.prime_interval_nat_ladder_c01201 n (by omega) (by omega)
