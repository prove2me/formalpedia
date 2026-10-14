-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T15:21:19.516126+00:00
-- url     : https://prove2.me/submissions/f068c815-55f5-48ce-a4c2-297e8558190c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05250

theorem solution (n : Nat)
    (hn : 5477696691841147 < n) (hupper : n <= 6309300846480967) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 5878812857266847 n with h2 | h2
  · -- n > 5878812857266847
    rcases Nat.lt_or_ge 6081645671724317 n with h4 | h4
    · -- n > 6081645671724317
      rcases Nat.lt_or_ge 6185671123801877 n with h6 | h6
      · -- n > 6185671123801877
        rcases Nat.lt_or_ge 6238353558244663 n with h8 | h8
        · -- n > 6238353558244663
          rcases Nat.lt_or_ge 6273726767154439 n with h10 | h10
          · -- n > 6273726767154439
            rcases Nat.lt_or_ge 6291488149303381 n with h12 | h12
            · -- n > 6291488149303381
              exact RamareSaouter2003.prime_interval_nat_ladder_c05250 n (by omega) (by omega)
            · -- n <= 6291488149303381
              exact RamareSaouter2003.prime_interval_nat_ladder_c05249 n (by omega) (by omega)
          · -- n <= 6273726767154439
            rcases Nat.lt_or_ge 6256014210815461 n with h12 | h12
            · -- n > 6256014210815461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05248 n (by omega) (by omega)
            · -- n <= 6256014210815461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05247 n (by omega) (by omega)
        · -- n <= 6238353558244663
          rcases Nat.lt_or_ge 6203182753629073 n with h10 | h10
          · -- n > 6203182753629073
            rcases Nat.lt_or_ge 6220743580262111 n with h12 | h12
            · -- n > 6220743580262111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05246 n (by omega) (by omega)
            · -- n <= 6220743580262111
              exact RamareSaouter2003.prime_interval_nat_ladder_c05245 n (by omega) (by omega)
          · -- n <= 6203182753629073
            exact RamareSaouter2003.prime_interval_nat_ladder_c05244 n (by omega) (by omega)
      · -- n <= 6185671123801877
        rcases Nat.lt_or_ge 6133431673599827 n with h8 | h8
        · -- n > 6133431673599827
          rcases Nat.lt_or_ge 6150797261562803 n with h10 | h10
          · -- n > 6150797261562803
            rcases Nat.lt_or_ge 6168207811473847 n with h12 | h12
            · -- n > 6168207811473847
              exact RamareSaouter2003.prime_interval_nat_ladder_c05243 n (by omega) (by omega)
            · -- n <= 6168207811473847
              exact RamareSaouter2003.prime_interval_nat_ladder_c05242 n (by omega) (by omega)
          · -- n <= 6150797261562803
            exact RamareSaouter2003.prime_interval_nat_ladder_c05241 n (by omega) (by omega)
        · -- n <= 6133431673599827
          rcases Nat.lt_or_ge 6098861469164987 n with h10 | h10
          · -- n > 6098861469164987
            rcases Nat.lt_or_ge 6116126930645899 n with h12 | h12
            · -- n > 6116126930645899
              exact RamareSaouter2003.prime_interval_nat_ladder_c05240 n (by omega) (by omega)
            · -- n <= 6116126930645899
              exact RamareSaouter2003.prime_interval_nat_ladder_c05239 n (by omega) (by omega)
          · -- n <= 6098861469164987
            exact RamareSaouter2003.prime_interval_nat_ladder_c05238 n (by omega) (by omega)
    · -- n <= 6081645671724317
      rcases Nat.lt_or_ge 5979376284678977 n with h6 | h6
      · -- n > 5979376284678977
        rcases Nat.lt_or_ge 6030297589561699 n with h8 | h8
        · -- n > 6030297589561699
          rcases Nat.lt_or_ge 6047370925927273 n with h10 | h10
          · -- n > 6047370925927273
            rcases Nat.lt_or_ge 6064490044896901 n with h12 | h12
            · -- n > 6064490044896901
              exact RamareSaouter2003.prime_interval_nat_ladder_c05237 n (by omega) (by omega)
            · -- n <= 6064490044896901
              exact RamareSaouter2003.prime_interval_nat_ladder_c05236 n (by omega) (by omega)
          · -- n <= 6047370925927273
            exact RamareSaouter2003.prime_interval_nat_ladder_c05235 n (by omega) (by omega)
        · -- n <= 6030297589561699
          rcases Nat.lt_or_ge 5996299993964561 n with h10 | h10
          · -- n > 5996299993964561
            rcases Nat.lt_or_ge 6013276622483099 n with h12 | h12
            · -- n > 6013276622483099
              exact RamareSaouter2003.prime_interval_nat_ladder_c05234 n (by omega) (by omega)
            · -- n <= 6013276622483099
              exact RamareSaouter2003.prime_interval_nat_ladder_c05233 n (by omega) (by omega)
          · -- n <= 5996299993964561
            exact RamareSaouter2003.prime_interval_nat_ladder_c05232 n (by omega) (by omega)
      · -- n <= 5979376284678977
        rcases Nat.lt_or_ge 5928881710133713 n with h8 | h8
        · -- n > 5928881710133713
          rcases Nat.lt_or_ge 5945667700557239 n with h10 | h10
          · -- n > 5945667700557239
            rcases Nat.lt_or_ge 5962499811203401 n with h12 | h12
            · -- n > 5962499811203401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05231 n (by omega) (by omega)
            · -- n <= 5962499811203401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05230 n (by omega) (by omega)
          · -- n <= 5945667700557239
            exact RamareSaouter2003.prime_interval_nat_ladder_c05229 n (by omega) (by omega)
        · -- n <= 5928881710133713
          rcases Nat.lt_or_ge 5895454316367311 n with h10 | h10
          · -- n > 5895454316367311
            rcases Nat.lt_or_ge 5912143128974461 n with h12 | h12
            · -- n > 5912143128974461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05228 n (by omega) (by omega)
            · -- n <= 5912143128974461
              exact RamareSaouter2003.prime_interval_nat_ladder_c05227 n (by omega) (by omega)
          · -- n <= 5895454316367311
            exact RamareSaouter2003.prime_interval_nat_ladder_c05226 n (by omega) (by omega)
  · -- n <= 5878812857266847
    rcases Nat.lt_or_ge 5666703374560037 n with h4 | h4
    · -- n > 5666703374560037
      rcases Nat.lt_or_ge 5763629572098011 n with h6 | h6
      · -- n > 5763629572098011
        rcases Nat.lt_or_ge 5812715845591363 n with h8 | h8
        · -- n > 5812715845591363
          rcases Nat.lt_or_ge 5845673757519649 n with h10 | h10
          · -- n > 5845673757519649
            rcases Nat.lt_or_ge 5862220957213051 n with h12 | h12
            · -- n > 5862220957213051
              exact RamareSaouter2003.prime_interval_nat_ladder_c05225 n (by omega) (by omega)
            · -- n <= 5862220957213051
              exact RamareSaouter2003.prime_interval_nat_ladder_c05224 n (by omega) (by omega)
          · -- n <= 5845673757519649
            rcases Nat.lt_or_ge 5829170403374177 n with h12 | h12
            · -- n > 5829170403374177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05223 n (by omega) (by omega)
            · -- n <= 5829170403374177
              exact RamareSaouter2003.prime_interval_nat_ladder_c05222 n (by omega) (by omega)
        · -- n <= 5812715845591363
          rcases Nat.lt_or_ge 5779947047186777 n with h10 | h10
          · -- n > 5779947047186777
            rcases Nat.lt_or_ge 5796305094574933 n with h12 | h12
            · -- n > 5796305094574933
              exact RamareSaouter2003.prime_interval_nat_ladder_c05221 n (by omega) (by omega)
            · -- n <= 5796305094574933
              exact RamareSaouter2003.prime_interval_nat_ladder_c05220 n (by omega) (by omega)
          · -- n <= 5779947047186777
            exact RamareSaouter2003.prime_interval_nat_ladder_c05219 n (by omega) (by omega)
      · -- n <= 5763629572098011
        rcases Nat.lt_or_ge 5714966136141209 n with h8 | h8
        · -- n > 5714966136141209
          rcases Nat.lt_or_ge 5731144674003911 n with h10 | h10
          · -- n > 5731144674003911
            rcases Nat.lt_or_ge 5747365186209281 n with h12 | h12
            · -- n > 5747365186209281
              exact RamareSaouter2003.prime_interval_nat_ladder_c05218 n (by omega) (by omega)
            · -- n <= 5747365186209281
              exact RamareSaouter2003.prime_interval_nat_ladder_c05217 n (by omega) (by omega)
          · -- n <= 5731144674003911
            exact RamareSaouter2003.prime_interval_nat_ladder_c05216 n (by omega) (by omega)
        · -- n <= 5714966136141209
          rcases Nat.lt_or_ge 5682746105830709 n with h10 | h10
          · -- n > 5682746105830709
            rcases Nat.lt_or_ge 5698833564109951 n with h12 | h12
            · -- n > 5698833564109951
              exact RamareSaouter2003.prime_interval_nat_ladder_c05215 n (by omega) (by omega)
            · -- n <= 5698833564109951
              exact RamareSaouter2003.prime_interval_nat_ladder_c05214 n (by omega) (by omega)
          · -- n <= 5682746105830709
            exact RamareSaouter2003.prime_interval_nat_ladder_c05213 n (by omega) (by omega)
    · -- n <= 5666703374560037
      rcases Nat.lt_or_ge 5571391613509879 n with h6 | h6
      · -- n > 5571391613509879
        rcases Nat.lt_or_ge 5618847800690743 n with h8 | h8
        · -- n > 5618847800690743
          rcases Nat.lt_or_ge 5634754842240791 n with h10 | h10
          · -- n > 5634754842240791
            rcases Nat.lt_or_ge 5650705713797161 n with h12 | h12
            · -- n > 5650705713797161
              exact RamareSaouter2003.prime_interval_nat_ladder_c05212 n (by omega) (by omega)
            · -- n <= 5650705713797161
              exact RamareSaouter2003.prime_interval_nat_ladder_c05211 n (by omega) (by omega)
          · -- n <= 5634754842240791
            exact RamareSaouter2003.prime_interval_nat_ladder_c05210 n (by omega) (by omega)
        · -- n <= 5618847800690743
          rcases Nat.lt_or_ge 5587165303968217 n with h10 | h10
          · -- n > 5587165303968217
            rcases Nat.lt_or_ge 5602984206450437 n with h12 | h12
            · -- n > 5602984206450437
              exact RamareSaouter2003.prime_interval_nat_ladder_c05209 n (by omega) (by omega)
            · -- n <= 5602984206450437
              exact RamareSaouter2003.prime_interval_nat_ladder_c05208 n (by omega) (by omega)
          · -- n <= 5587165303968217
            exact RamareSaouter2003.prime_interval_nat_ladder_c05207 n (by omega) (by omega)
      · -- n <= 5571391613509879
        rcases Nat.lt_or_ge 5524345238481203 n with h8 | h8
        · -- n > 5524345238481203
          rcases Nat.lt_or_ge 5539984654522057 n with h10 | h10
          · -- n > 5539984654522057
            rcases Nat.lt_or_ge 5555664366106853 n with h12 | h12
            · -- n > 5555664366106853
              exact RamareSaouter2003.prime_interval_nat_ladder_c05206 n (by omega) (by omega)
            · -- n <= 5555664366106853
              exact RamareSaouter2003.prime_interval_nat_ladder_c05205 n (by omega) (by omega)
          · -- n <= 5539984654522057
            exact RamareSaouter2003.prime_interval_nat_ladder_c05204 n (by omega) (by omega)
        · -- n <= 5524345238481203
          rcases Nat.lt_or_ge 5493205354621591 n with h10 | h10
          · -- n > 5493205354621591
            rcases Nat.lt_or_ge 5508749447974909 n with h12 | h12
            · -- n > 5508749447974909
              exact RamareSaouter2003.prime_interval_nat_ladder_c05203 n (by omega) (by omega)
            · -- n <= 5508749447974909
              exact RamareSaouter2003.prime_interval_nat_ladder_c05202 n (by omega) (by omega)
          · -- n <= 5493205354621591
            exact RamareSaouter2003.prime_interval_nat_ladder_c05201 n (by omega) (by omega)
