-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T13:31:12.189982+00:00
-- url     : https://prove2.me/submissions/3b5560d5-3cce-44f2-8517-7bd55b6d334a

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08250
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08276

theorem solution (n : Nat)
    (hn : 26882311053914850133 < n) (hupper : n <= 30299003920194604927) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 28504751089404134399 n with h2 | h2
  · -- n > 28504751089404134399
    rcases Nat.lt_or_ge 29352329368012762843 n with h4 | h4
    · -- n > 29352329368012762843
      rcases Nat.lt_or_ge 29785523491525632349 n with h6 | h6
      · -- n > 29785523491525632349
        rcases Nat.lt_or_ge 30004512388881891031 n with h8 | h8
        · -- n > 30004512388881891031
          rcases Nat.lt_or_ge 30151398509990116207 n with h10 | h10
          · -- n > 30151398509990116207
            rcases Nat.lt_or_ge 30225111230054480669 n with h12 | h12
            · -- n > 30225111230054480669
              exact RamareSaouter2003.prime_interval_nat_ladder_c08276 n (by omega) (by omega)
            · -- n <= 30225111230054480669
              exact RamareSaouter2003.prime_interval_nat_ladder_c08275 n (by omega) (by omega)
          · -- n <= 30151398509990116207
            rcases Nat.lt_or_ge 30077865859299267221 n with h12 | h12
            · -- n > 30077865859299267221
              exact RamareSaouter2003.prime_interval_nat_ladder_c08274 n (by omega) (by omega)
            · -- n <= 30077865859299267221
              exact RamareSaouter2003.prime_interval_nat_ladder_c08273 n (by omega) (by omega)
        · -- n <= 30004512388881891031
          rcases Nat.lt_or_ge 29858341591879119533 n with h10 | h10
          · -- n > 29858341591879119533
            rcases Nat.lt_or_ge 29931337738758882739 n with h12 | h12
            · -- n > 29931337738758882739
              exact RamareSaouter2003.prime_interval_nat_ladder_c08272 n (by omega) (by omega)
            · -- n <= 29931337738758882739
              exact RamareSaouter2003.prime_interval_nat_ladder_c08271 n (by omega) (by omega)
          · -- n <= 29858341591879119533
            exact RamareSaouter2003.prime_interval_nat_ladder_c08270 n (by omega) (by omega)
      · -- n <= 29785523491525632349
        rcases Nat.lt_or_ge 29568133338108854549 n with h8 | h8
        · -- n > 29568133338108854549
          rcases Nat.lt_or_ge 29640419896826981621 n with h10 | h10
          · -- n > 29640419896826981621
            rcases Nat.lt_or_ge 29712883373121522569 n with h12 | h12
            · -- n > 29712883373121522569
              exact RamareSaouter2003.prime_interval_nat_ladder_c08269 n (by omega) (by omega)
            · -- n <= 29712883373121522569
              exact RamareSaouter2003.prime_interval_nat_ladder_c08268 n (by omega) (by omega)
          · -- n <= 29640419896826981621
            exact RamareSaouter2003.prime_interval_nat_ladder_c08267 n (by omega) (by omega)
        · -- n <= 29568133338108854549
          rcases Nat.lt_or_ge 29424088531903710179 n with h10 | h10
          · -- n > 29424088531903710179
            rcases Nat.lt_or_ge 29496023103755818367 n with h12 | h12
            · -- n > 29496023103755818367
              exact RamareSaouter2003.prime_interval_nat_ladder_c08266 n (by omega) (by omega)
            · -- n <= 29496023103755818367
              exact RamareSaouter2003.prime_interval_nat_ladder_c08265 n (by omega) (by omega)
          · -- n <= 29424088531903710179
            exact RamareSaouter2003.prime_interval_nat_ladder_c08264 n (by omega) (by omega)
    · -- n <= 29352329368012762843
      rcases Nat.lt_or_ge 28925436206231189263 n with h6 | h6
      · -- n > 28925436206231189263
        rcases Nat.lt_or_ge 29138100388269164063 n with h8 | h8
        · -- n > 29138100388269164063
          rcases Nat.lt_or_ge 29209335848980807357 n with h10 | h10
          · -- n > 29209335848980807357
            rcases Nat.lt_or_ge 29280745463474841263 n with h12 | h12
            · -- n > 29280745463474841263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08263 n (by omega) (by omega)
            · -- n <= 29280745463474841263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08262 n (by omega) (by omega)
          · -- n <= 29209335848980807357
            exact RamareSaouter2003.prime_interval_nat_ladder_c08261 n (by omega) (by omega)
        · -- n <= 29138100388269164063
          rcases Nat.lt_or_ge 28996151629608908209 n with h10 | h10
          · -- n > 28996151629608908209
            rcases Nat.lt_or_ge 29067039962792056273 n with h12 | h12
            · -- n > 29067039962792056273
              exact RamareSaouter2003.prime_interval_nat_ladder_c08260 n (by omega) (by omega)
            · -- n <= 29067039962792056273
              exact RamareSaouter2003.prime_interval_nat_ladder_c08259 n (by omega) (by omega)
          · -- n <= 28996151629608908209
            exact RamareSaouter2003.prime_interval_nat_ladder_c08258 n (by omega) (by omega)
      · -- n <= 28925436206231189263
        rcases Nat.lt_or_ge 28714323536888791261 n with h8 | h8
        · -- n > 28714323536888791261
          rcases Nat.lt_or_ge 28784522609150254747 n with h10 | h10
          · -- n > 28784522609150254747
            rcases Nat.lt_or_ge 28854893505109758287 n with h12 | h12
            · -- n > 28854893505109758287
              exact RamareSaouter2003.prime_interval_nat_ladder_c08257 n (by omega) (by omega)
            · -- n <= 28854893505109758287
              exact RamareSaouter2003.prime_interval_nat_ladder_c08256 n (by omega) (by omega)
          · -- n <= 28784522609150254747
            exact RamareSaouter2003.prime_interval_nat_ladder_c08255 n (by omega) (by omega)
        · -- n <= 28714323536888791261
          rcases Nat.lt_or_ge 28574438126674727123 n with h10 | h10
          · -- n > 28574438126674727123
            rcases Nat.lt_or_ge 28644295555126805263 n with h12 | h12
            · -- n > 28644295555126805263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08254 n (by omega) (by omega)
            · -- n <= 28644295555126805263
              exact RamareSaouter2003.prime_interval_nat_ladder_c08253 n (by omega) (by omega)
          · -- n <= 28574438126674727123
            exact RamareSaouter2003.prime_interval_nat_ladder_c08252 n (by omega) (by omega)
  · -- n <= 28504751089404134399
    rcases Nat.lt_or_ge 27681647049976368833 n with h4 | h4
    · -- n > 27681647049976368833
      rcases Nat.lt_or_ge 28090184277367654901 n with h6 | h6
      · -- n > 28090184277367654901
        rcases Nat.lt_or_ge 28296708643719741271 n with h8 | h8
        · -- n > 28296708643719741271
          rcases Nat.lt_or_ge 28365886866662883911 n with h10 | h10
          · -- n > 28365886866662883911
            rcases Nat.lt_or_ge 28435234280782969603 n with h12 | h12
            · -- n > 28435234280782969603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08251 n (by omega) (by omega)
            · -- n <= 28435234280782969603
              exact RamareSaouter2003.prime_interval_nat_ladder_c08250 n (by omega) (by omega)
          · -- n <= 28365886866662883911
            exact RamareSaouter2003.prime_interval_nat_ladder_c08249 n (by omega) (by omega)
        · -- n <= 28296708643719741271
          rcases Nat.lt_or_ge 28158857620262503583 n with h10 | h10
          · -- n > 28158857620262503583
            rcases Nat.lt_or_ge 28227698919821419757 n with h12 | h12
            · -- n > 28227698919821419757
              exact RamareSaouter2003.prime_interval_nat_ladder_c08248 n (by omega) (by omega)
            · -- n <= 28227698919821419757
              exact RamareSaouter2003.prime_interval_nat_ladder_c08247 n (by omega) (by omega)
          · -- n <= 28158857620262503583
            exact RamareSaouter2003.prime_interval_nat_ladder_c08246 n (by omega) (by omega)
      · -- n <= 28090184277367654901
        rcases Nat.lt_or_ge 27885167459867124413 n with h8 | h8
        · -- n > 27885167459867124413
          rcases Nat.lt_or_ge 27953339757179896201 n with h10 | h10
          · -- n > 27953339757179896201
            rcases Nat.lt_or_ge 28021678743043794359 n with h12 | h12
            · -- n > 28021678743043794359
              exact RamareSaouter2003.prime_interval_nat_ladder_c08245 n (by omega) (by omega)
            · -- n <= 28021678743043794359
              exact RamareSaouter2003.prime_interval_nat_ladder_c08244 n (by omega) (by omega)
          · -- n <= 27953339757179896201
            exact RamareSaouter2003.prime_interval_nat_ladder_c08243 n (by omega) (by omega)
        · -- n <= 27885167459867124413
          rcases Nat.lt_or_ge 27749321415470955169 n with h10 | h10
          · -- n > 27749321415470955169
            rcases Nat.lt_or_ge 27817161556360991819 n with h12 | h12
            · -- n > 27817161556360991819
              exact RamareSaouter2003.prime_interval_nat_ladder_c08242 n (by omega) (by omega)
            · -- n <= 27817161556360991819
              exact RamareSaouter2003.prime_interval_nat_ladder_c08241 n (by omega) (by omega)
          · -- n <= 27749321415470955169
            exact RamareSaouter2003.prime_interval_nat_ladder_c08240 n (by omega) (by omega)
    · -- n <= 27681647049976368833
      rcases Nat.lt_or_ge 27279051834621910273 n with h6 | h6
      · -- n > 27279051834621910273
        rcases Nat.lt_or_ge 27479612440243052527 n with h8 | h8
        · -- n > 27479612440243052527
          rcases Nat.lt_or_ge 27546792506037507071 n with h10 | h10
          · -- n > 27546792506037507071
            rcases Nat.lt_or_ge 27614137545736712381 n with h12 | h12
            · -- n > 27614137545736712381
              exact RamareSaouter2003.prime_interval_nat_ladder_c08239 n (by omega) (by omega)
            · -- n <= 27614137545736712381
              exact RamareSaouter2003.prime_interval_nat_ladder_c08238 n (by omega) (by omega)
          · -- n <= 27546792506037507071
            exact RamareSaouter2003.prime_interval_nat_ladder_c08237 n (by omega) (by omega)
        · -- n <= 27479612440243052527
          rcases Nat.lt_or_ge 27345742003831345037 n with h10 | h10
          · -- n > 27345742003831345037
            rcases Nat.lt_or_ge 27412595512281703033 n with h12 | h12
            · -- n > 27412595512281703033
              exact RamareSaouter2003.prime_interval_nat_ladder_c08236 n (by omega) (by omega)
            · -- n <= 27412595512281703033
              exact RamareSaouter2003.prime_interval_nat_ladder_c08235 n (by omega) (by omega)
          · -- n <= 27345742003831345037
            exact RamareSaouter2003.prime_interval_nat_ladder_c08234 n (by omega) (by omega)
      · -- n <= 27279051834621910273
        rcases Nat.lt_or_ge 27079954893869532133 n with h8 | h8
        · -- n > 27079954893869532133
          rcases Nat.lt_or_ge 27146158706657057891 n with h10 | h10
          · -- n > 27146158706657057891
            rcases Nat.lt_or_ge 27212524202288191469 n with h12 | h12
            · -- n > 27212524202288191469
              exact RamareSaouter2003.prime_interval_nat_ladder_c08233 n (by omega) (by omega)
            · -- n <= 27212524202288191469
              exact RamareSaouter2003.prime_interval_nat_ladder_c08232 n (by omega) (by omega)
          · -- n <= 27146158706657057891
            exact RamareSaouter2003.prime_interval_nat_ladder_c08231 n (by omega) (by omega)
        · -- n <= 27079954893869532133
          rcases Nat.lt_or_ge 26948031649233508711 n with h10 | h10
          · -- n > 26948031649233508711
            rcases Nat.lt_or_ge 27013912927425032683 n with h12 | h12
            · -- n > 27013912927425032683
              exact RamareSaouter2003.prime_interval_nat_ladder_c08230 n (by omega) (by omega)
            · -- n <= 27013912927425032683
              exact RamareSaouter2003.prime_interval_nat_ladder_c08229 n (by omega) (by omega)
          · -- n <= 26948031649233508711
            exact RamareSaouter2003.prime_interval_nat_ladder_c08228 n (by omega) (by omega)
