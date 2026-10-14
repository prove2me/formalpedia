-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T03:08:42.140927+00:00
-- url     : https://prove2.me/submissions/1e80fcbf-3b14-44eb-9bcb-4dcc55c21126

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03250

theorem solution (n : Nat)
    (hn : 24876889450507 < n) (hupper : n <= 28149319776593) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 26462568208057 n with h2 | h2
  · -- n > 26462568208057
    rcases Nat.lt_or_ge 27259207733287 n with h4 | h4
    · -- n > 27259207733287
      rcases Nat.lt_or_ge 27666476254943 n with h6 | h6
      · -- n > 27666476254943
        rcases Nat.lt_or_ge 27872386676891 n with h8 | h8
        · -- n > 27872386676891
          rcases Nat.lt_or_ge 28010510982581 n with h10 | h10
          · -- n > 28010510982581
            rcases Nat.lt_or_ge 28079829606949 n with h12 | h12
            · -- n > 28079829606949
              exact RamareSaouter2003.prime_interval_nat_ladder_c03250 n (by omega) (by omega)
            · -- n <= 28079829606949
              exact RamareSaouter2003.prime_interval_nat_ladder_c03249 n (by omega) (by omega)
          · -- n <= 28010510982581
            rcases Nat.lt_or_ge 27941363480011 n with h12 | h12
            · -- n > 27941363480011
              exact RamareSaouter2003.prime_interval_nat_ladder_c03248 n (by omega) (by omega)
            · -- n <= 27941363480011
              exact RamareSaouter2003.prime_interval_nat_ladder_c03247 n (by omega) (by omega)
        · -- n <= 27872386676891
          rcases Nat.lt_or_ge 27734943484181 n with h10 | h10
          · -- n > 27734943484181
            rcases Nat.lt_or_ge 27803580151747 n with h12 | h12
            · -- n > 27803580151747
              exact RamareSaouter2003.prime_interval_nat_ladder_c03246 n (by omega) (by omega)
            · -- n <= 27803580151747
              exact RamareSaouter2003.prime_interval_nat_ladder_c03245 n (by omega) (by omega)
          · -- n <= 27734943484181
            exact RamareSaouter2003.prime_interval_nat_ladder_c03244 n (by omega) (by omega)
      · -- n <= 27666476254943
        rcases Nat.lt_or_ge 27462087019669 n with h8 | h8
        · -- n > 27462087019669
          rcases Nat.lt_or_ge 27530048439427 n with h10 | h10
          · -- n > 27530048439427
            rcases Nat.lt_or_ge 27598178045803 n with h12 | h12
            · -- n > 27598178045803
              exact RamareSaouter2003.prime_interval_nat_ladder_c03243 n (by omega) (by omega)
            · -- n <= 27598178045803
              exact RamareSaouter2003.prime_interval_nat_ladder_c03242 n (by omega) (by omega)
          · -- n <= 27530048439427
            exact RamareSaouter2003.prime_interval_nat_ladder_c03241 n (by omega) (by omega)
        · -- n <= 27462087019669
          rcases Nat.lt_or_ge 27326667080183 n with h10 | h10
          · -- n > 27326667080183
            rcases Nat.lt_or_ge 27394293371287 n with h12 | h12
            · -- n > 27394293371287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03240 n (by omega) (by omega)
            · -- n <= 27394293371287
              exact RamareSaouter2003.prime_interval_nat_ladder_c03239 n (by omega) (by omega)
          · -- n <= 27326667080183
            exact RamareSaouter2003.prime_interval_nat_ladder_c03238 n (by omega) (by omega)
    · -- n <= 27259207733287
      rcases Nat.lt_or_ge 26857934469071 n with h6 | h6
      · -- n > 26857934469071
        rcases Nat.lt_or_ge 27057827240501 n with h8 | h8
        · -- n > 27057827240501
          rcases Nat.lt_or_ge 27124788223993 n with h10 | h10
          · -- n > 27124788223993
            rcases Nat.lt_or_ge 27191914918249 n with h12 | h12
            · -- n > 27191914918249
              exact RamareSaouter2003.prime_interval_nat_ladder_c03237 n (by omega) (by omega)
            · -- n <= 27191914918249
              exact RamareSaouter2003.prime_interval_nat_ladder_c03236 n (by omega) (by omega)
          · -- n <= 27124788223993
            exact RamareSaouter2003.prime_interval_nat_ladder_c03235 n (by omega) (by omega)
        · -- n <= 27057827240501
          rcases Nat.lt_or_ge 26924400770599 n with h10 | h10
          · -- n > 26924400770599
            rcases Nat.lt_or_ge 26991031558807 n with h12 | h12
            · -- n > 26991031558807
              exact RamareSaouter2003.prime_interval_nat_ladder_c03234 n (by omega) (by omega)
            · -- n <= 26991031558807
              exact RamareSaouter2003.prime_interval_nat_ladder_c03233 n (by omega) (by omega)
          · -- n <= 26924400770599
            exact RamareSaouter2003.prime_interval_nat_ladder_c03232 n (by omega) (by omega)
      · -- n <= 26857934469071
        rcases Nat.lt_or_ge 26659518428063 n with h8 | h8
        · -- n > 26659518428063
          rcases Nat.lt_or_ge 26725493702363 n with h10 | h10
          · -- n > 26725493702363
            rcases Nat.lt_or_ge 26791632248033 n with h12 | h12
            · -- n > 26791632248033
              exact RamareSaouter2003.prime_interval_nat_ladder_c03231 n (by omega) (by omega)
            · -- n <= 26791632248033
              exact RamareSaouter2003.prime_interval_nat_ladder_c03230 n (by omega) (by omega)
          · -- n <= 26725493702363
            exact RamareSaouter2003.prime_interval_nat_ladder_c03229 n (by omega) (by omega)
        · -- n <= 26659518428063
          rcases Nat.lt_or_ge 26528056082441 n with h10 | h10
          · -- n > 26528056082441
            rcases Nat.lt_or_ge 26593706022119 n with h12 | h12
            · -- n > 26593706022119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03228 n (by omega) (by omega)
            · -- n <= 26593706022119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03227 n (by omega) (by omega)
          · -- n <= 26528056082441
            exact RamareSaouter2003.prime_interval_nat_ladder_c03226 n (by omega) (by omega)
  · -- n <= 26462568208057
    rcases Nat.lt_or_ge 25625793080143 n with h4 | h4
    · -- n > 25625793080143
      rcases Nat.lt_or_ge 26008657430653 n with h6 | h6
      · -- n > 26008657430653
        rcases Nat.lt_or_ge 26202229375667 n with h8 | h8
        · -- n > 26202229375667
          rcases Nat.lt_or_ge 26332077055483 n with h10 | h10
          · -- n > 26332077055483
            rcases Nat.lt_or_ge 26397241998779 n with h12 | h12
            · -- n > 26397241998779
              exact RamareSaouter2003.prime_interval_nat_ladder_c03225 n (by omega) (by omega)
            · -- n <= 26397241998779
              exact RamareSaouter2003.prime_interval_nat_ladder_c03224 n (by omega) (by omega)
          · -- n <= 26332077055483
            rcases Nat.lt_or_ge 26267072980129 n with h12 | h12
            · -- n > 26267072980129
              exact RamareSaouter2003.prime_interval_nat_ladder_c03223 n (by omega) (by omega)
            · -- n <= 26267072980129
              exact RamareSaouter2003.prime_interval_nat_ladder_c03222 n (by omega) (by omega)
        · -- n <= 26202229375667
          rcases Nat.lt_or_ge 26073021995663 n with h10 | h10
          · -- n > 26073021995663
            rcases Nat.lt_or_ge 26137545845951 n with h12 | h12
            · -- n > 26137545845951
              exact RamareSaouter2003.prime_interval_nat_ladder_c03221 n (by omega) (by omega)
            · -- n <= 26137545845951
              exact RamareSaouter2003.prime_interval_nat_ladder_c03220 n (by omega) (by omega)
          · -- n <= 26073021995663
            exact RamareSaouter2003.prime_interval_nat_ladder_c03219 n (by omega) (by omega)
      · -- n <= 26008657430653
        rcases Nat.lt_or_ge 25816515520249 n with h8 | h8
        · -- n > 25816515520249
          rcases Nat.lt_or_ge 25880404584667 n with h10 | h10
          · -- n > 25880404584667
            rcases Nat.lt_or_ge 25944451757753 n with h12 | h12
            · -- n > 25944451757753
              exact RamareSaouter2003.prime_interval_nat_ladder_c03218 n (by omega) (by omega)
            · -- n <= 25944451757753
              exact RamareSaouter2003.prime_interval_nat_ladder_c03217 n (by omega) (by omega)
          · -- n <= 25880404584667
            exact RamareSaouter2003.prime_interval_nat_ladder_c03216 n (by omega) (by omega)
        · -- n <= 25816515520249
          rcases Nat.lt_or_ge 25689210156919 n with h10 | h10
          · -- n > 25689210156919
            rcases Nat.lt_or_ge 25752784174153 n with h12 | h12
            · -- n > 25752784174153
              exact RamareSaouter2003.prime_interval_nat_ladder_c03215 n (by omega) (by omega)
            · -- n <= 25752784174153
              exact RamareSaouter2003.prime_interval_nat_ladder_c03214 n (by omega) (by omega)
          · -- n <= 25689210156919
            exact RamareSaouter2003.prime_interval_nat_ladder_c03213 n (by omega) (by omega)
    · -- n <= 25625793080143
      rcases Nat.lt_or_ge 25248564742361 n with h6 | h6
      · -- n > 25248564742361
        rcases Nat.lt_or_ge 25436479624163 n with h8 | h8
        · -- n > 25436479624163
          rcases Nat.lt_or_ge 25499428199701 n with h10 | h10
          · -- n > 25499428199701
            rcases Nat.lt_or_ge 25562532556751 n with h12 | h12
            · -- n > 25562532556751
              exact RamareSaouter2003.prime_interval_nat_ladder_c03212 n (by omega) (by omega)
            · -- n <= 25562532556751
              exact RamareSaouter2003.prime_interval_nat_ladder_c03211 n (by omega) (by omega)
          · -- n <= 25499428199701
            exact RamareSaouter2003.prime_interval_nat_ladder_c03210 n (by omega) (by omega)
        · -- n <= 25436479624163
          rcases Nat.lt_or_ge 25311048278401 n with h10 | h10
          · -- n > 25311048278401
            rcases Nat.lt_or_ge 25373686444793 n with h12 | h12
            · -- n > 25373686444793
              exact RamareSaouter2003.prime_interval_nat_ladder_c03209 n (by omega) (by omega)
            · -- n <= 25373686444793
              exact RamareSaouter2003.prime_interval_nat_ladder_c03208 n (by omega) (by omega)
          · -- n <= 25311048278401
            exact RamareSaouter2003.prime_interval_nat_ladder_c03207 n (by omega) (by omega)
      · -- n <= 25248564742361
        rcases Nat.lt_or_ge 25062038103181 n with h8 | h8
        · -- n > 25062038103181
          rcases Nat.lt_or_ge 25124060034961 n with h10 | h10
          · -- n > 25124060034961
            rcases Nat.lt_or_ge 25186235454791 n with h12 | h12
            · -- n > 25186235454791
              exact RamareSaouter2003.prime_interval_nat_ladder_c03206 n (by omega) (by omega)
            · -- n <= 25186235454791
              exact RamareSaouter2003.prime_interval_nat_ladder_c03205 n (by omega) (by omega)
          · -- n <= 25124060034961
            exact RamareSaouter2003.prime_interval_nat_ladder_c03204 n (by omega) (by omega)
        · -- n <= 25062038103181
          rcases Nat.lt_or_ge 24938453188349 n with h10 | h10
          · -- n > 24938453188349
            rcases Nat.lt_or_ge 25000169280221 n with h12 | h12
            · -- n > 25000169280221
              exact RamareSaouter2003.prime_interval_nat_ladder_c03203 n (by omega) (by omega)
            · -- n <= 25000169280221
              exact RamareSaouter2003.prime_interval_nat_ladder_c03202 n (by omega) (by omega)
          · -- n <= 24938453188349
            exact RamareSaouter2003.prime_interval_nat_ladder_c03201 n (by omega) (by omega)
