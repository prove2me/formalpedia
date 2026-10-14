-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T09:41:16.494228+00:00
-- url     : https://prove2.me/submissions/a534fee4-f04f-4d81-9b18-9203ab2a38a9

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04247
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04250

theorem solution (n : Nat)
    (hn : 324415616742421 < n) (hupper : n <= 373647047298709) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 348160487597353 n with h2 | h2
  · -- n > 348160487597353
    rcases Nat.lt_or_ge 360169840580051 n with h4 | h4
    · -- n > 360169840580051
      rcases Nat.lt_or_ge 366330186786481 n with h6 | h6
      · -- n > 366330186786481
        rcases Nat.lt_or_ge 369446421091621 n with h8 | h8
        · -- n > 369446421091621
          rcases Nat.lt_or_ge 371541009448291 n with h10 | h10
          · -- n > 371541009448291
            rcases Nat.lt_or_ge 372592454438423 n with h12 | h12
            · -- n > 372592454438423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04250 n (by omega) (by omega)
            · -- n <= 372592454438423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04249 n (by omega) (by omega)
          · -- n <= 371541009448291
            rcases Nat.lt_or_ge 370492359467029 n with h12 | h12
            · -- n > 370492359467029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04248 n (by omega) (by omega)
            · -- n <= 370492359467029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04247 n (by omega) (by omega)
        · -- n <= 369446421091621
          rcases Nat.lt_or_ge 367364921716213 n with h10 | h10
          · -- n > 367364921716213
            rcases Nat.lt_or_ge 368404956363439 n with h12 | h12
            · -- n > 368404956363439
              exact RamareSaouter2003.prime_interval_nat_ladder_c04246 n (by omega) (by omega)
            · -- n <= 368404956363439
              exact RamareSaouter2003.prime_interval_nat_ladder_c04245 n (by omega) (by omega)
          · -- n <= 367364921716213
            exact RamareSaouter2003.prime_interval_nat_ladder_c04244 n (by omega) (by omega)
      · -- n <= 366330186786481
        rcases Nat.lt_or_ge 363237023164199 n with h8 | h8
        · -- n > 363237023164199
          rcases Nat.lt_or_ge 364265436646313 n with h10 | h10
          · -- n > 364265436646313
            rcases Nat.lt_or_ge 365296145297359 n with h12 | h12
            · -- n > 365296145297359
              exact RamareSaouter2003.prime_interval_nat_ladder_c04243 n (by omega) (by omega)
            · -- n <= 365296145297359
              exact RamareSaouter2003.prime_interval_nat_ladder_c04242 n (by omega) (by omega)
          · -- n <= 364265436646313
            exact RamareSaouter2003.prime_interval_nat_ladder_c04241 n (by omega) (by omega)
        · -- n <= 363237023164199
          rcases Nat.lt_or_ge 361189345243399 n with h10 | h10
          · -- n > 361189345243399
            rcases Nat.lt_or_ge 362211661496221 n with h12 | h12
            · -- n > 362211661496221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04240 n (by omega) (by omega)
            · -- n <= 362211661496221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04239 n (by omega) (by omega)
          · -- n <= 361189345243399
            exact RamareSaouter2003.prime_interval_nat_ladder_c04238 n (by omega) (by omega)
    · -- n <= 360169840580051
      rcases Nat.lt_or_ge 354115133523631 n with h6 | h6
      · -- n > 354115133523631
        rcases Nat.lt_or_ge 357128475211019 n with h8 | h8
        · -- n > 357128475211019
          rcases Nat.lt_or_ge 358139580419681 n with h10 | h10
          · -- n > 358139580419681
            rcases Nat.lt_or_ge 359153064838727 n with h12 | h12
            · -- n > 359153064838727
              exact RamareSaouter2003.prime_interval_nat_ladder_c04237 n (by omega) (by omega)
            · -- n <= 359153064838727
              exact RamareSaouter2003.prime_interval_nat_ladder_c04236 n (by omega) (by omega)
          · -- n <= 358139580419681
            exact RamareSaouter2003.prime_interval_nat_ladder_c04235 n (by omega) (by omega)
        · -- n <= 357128475211019
          rcases Nat.lt_or_ge 355116013864951 n with h10 | h10
          · -- n > 355116013864951
            rcases Nat.lt_or_ge 356120269037111 n with h12 | h12
            · -- n > 356120269037111
              exact RamareSaouter2003.prime_interval_nat_ladder_c04234 n (by omega) (by omega)
            · -- n <= 356120269037111
              exact RamareSaouter2003.prime_interval_nat_ladder_c04233 n (by omega) (by omega)
          · -- n <= 355116013864951
            exact RamareSaouter2003.prime_interval_nat_ladder_c04232 n (by omega) (by omega)
      · -- n <= 354115133523631
        rcases Nat.lt_or_ge 351125015870767 n with h8 | h8
        · -- n > 351125015870767
          rcases Nat.lt_or_ge 352118812571753 n with h10 | h10
          · -- n > 352118812571753
            rcases Nat.lt_or_ge 353115516786029 n with h12 | h12
            · -- n > 353115516786029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04231 n (by omega) (by omega)
            · -- n <= 353115516786029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04230 n (by omega) (by omega)
          · -- n <= 352118812571753
            exact RamareSaouter2003.prime_interval_nat_ladder_c04229 n (by omega) (by omega)
        · -- n <= 351125015870767
          rcases Nat.lt_or_ge 349146234458927 n with h10 | h10
          · -- n > 349146234458927
            rcases Nat.lt_or_ge 350134570877501 n with h12 | h12
            · -- n > 350134570877501
              exact RamareSaouter2003.prime_interval_nat_ladder_c04228 n (by omega) (by omega)
            · -- n <= 350134570877501
              exact RamareSaouter2003.prime_interval_nat_ladder_c04227 n (by omega) (by omega)
          · -- n <= 349146234458927
            exact RamareSaouter2003.prime_interval_nat_ladder_c04226 n (by omega) (by omega)
  · -- n <= 348160487597353
    rcases Nat.lt_or_ge 335603134842271 n with h4 | h4
    · -- n > 335603134842271
      rcases Nat.lt_or_ge 341341372797833 n with h6 | h6
      · -- n > 341341372797833
        rcases Nat.lt_or_ge 344247099914819 n with h8 | h8
        · -- n > 344247099914819
          rcases Nat.lt_or_ge 346198536740653 n with h10 | h10
          · -- n > 346198536740653
            rcases Nat.lt_or_ge 347177663220931 n with h12 | h12
            · -- n > 347177663220931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04225 n (by omega) (by omega)
            · -- n <= 347177663220931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04224 n (by omega) (by omega)
          · -- n <= 346198536740653
            rcases Nat.lt_or_ge 345221310905201 n with h12 | h12
            · -- n > 345221310905201
              exact RamareSaouter2003.prime_interval_nat_ladder_c04223 n (by omega) (by omega)
            · -- n <= 345221310905201
              exact RamareSaouter2003.prime_interval_nat_ladder_c04222 n (by omega) (by omega)
        · -- n <= 344247099914819
          rcases Nat.lt_or_ge 342306913516079 n with h10 | h10
          · -- n > 342306913516079
            rcases Nat.lt_or_ge 343275561685409 n with h12 | h12
            · -- n > 343275561685409
              exact RamareSaouter2003.prime_interval_nat_ladder_c04221 n (by omega) (by omega)
            · -- n <= 343275561685409
              exact RamareSaouter2003.prime_interval_nat_ladder_c04220 n (by omega) (by omega)
          · -- n <= 342306913516079
            exact RamareSaouter2003.prime_interval_nat_ladder_c04219 n (by omega) (by omega)
      · -- n <= 341341372797833
        rcases Nat.lt_or_ge 338460948320479 n with h8 | h8
        · -- n > 338460948320479
          rcases Nat.lt_or_ge 339417878876449 n with h10 | h10
          · -- n > 339417878876449
            rcases Nat.lt_or_ge 340377857661931 n with h12 | h12
            · -- n > 340377857661931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04218 n (by omega) (by omega)
            · -- n <= 340377857661931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04217 n (by omega) (by omega)
          · -- n <= 339417878876449
            exact RamareSaouter2003.prime_interval_nat_ladder_c04216 n (by omega) (by omega)
        · -- n <= 338460948320479
          rcases Nat.lt_or_ge 336553048207979 n with h10 | h10
          · -- n > 336553048207979
            rcases Nat.lt_or_ge 337505809826993 n with h12 | h12
            · -- n > 337505809826993
              exact RamareSaouter2003.prime_interval_nat_ladder_c04215 n (by omega) (by omega)
            · -- n <= 337505809826993
              exact RamareSaouter2003.prime_interval_nat_ladder_c04214 n (by omega) (by omega)
          · -- n <= 336553048207979
            exact RamareSaouter2003.prime_interval_nat_ladder_c04213 n (by omega) (by omega)
    · -- n <= 335603134842271
      rcases Nat.lt_or_ge 329961927200303 n with h6 | h6
      · -- n > 329961927200303
        rcases Nat.lt_or_ge 332770170136121 n with h8 | h8
        · -- n > 332770170136121
          rcases Nat.lt_or_ge 333712268789651 n with h10 | h10
          · -- n > 333712268789651
            rcases Nat.lt_or_ge 334656502991257 n with h12 | h12
            · -- n > 334656502991257
              exact RamareSaouter2003.prime_interval_nat_ladder_c04212 n (by omega) (by omega)
            · -- n <= 334656502991257
              exact RamareSaouter2003.prime_interval_nat_ladder_c04211 n (by omega) (by omega)
          · -- n <= 333712268789651
            exact RamareSaouter2003.prime_interval_nat_ladder_c04210 n (by omega) (by omega)
        · -- n <= 332770170136121
          rcases Nat.lt_or_ge 330895826095909 n with h10 | h10
          · -- n > 330895826095909
            rcases Nat.lt_or_ge 331831844350309 n with h12 | h12
            · -- n > 331831844350309
              exact RamareSaouter2003.prime_interval_nat_ladder_c04209 n (by omega) (by omega)
            · -- n <= 331831844350309
              exact RamareSaouter2003.prime_interval_nat_ladder_c04208 n (by omega) (by omega)
          · -- n <= 330895826095909
            exact RamareSaouter2003.prime_interval_nat_ladder_c04207 n (by omega) (by omega)
      · -- n <= 329961927200303
        rcases Nat.lt_or_ge 327178356916129 n with h8 | h8
        · -- n > 327178356916129
          rcases Nat.lt_or_ge 328104542198201 n with h10 | h10
          · -- n > 328104542198201
            rcases Nat.lt_or_ge 329032652152459 n with h12 | h12
            · -- n > 329032652152459
              exact RamareSaouter2003.prime_interval_nat_ladder_c04206 n (by omega) (by omega)
            · -- n <= 329032652152459
              exact RamareSaouter2003.prime_interval_nat_ladder_c04205 n (by omega) (by omega)
          · -- n <= 328104542198201
            exact RamareSaouter2003.prime_interval_nat_ladder_c04204 n (by omega) (by omega)
        · -- n <= 327178356916129
          rcases Nat.lt_or_ge 325333774467313 n with h10 | h10
          · -- n > 325333774467313
            rcases Nat.lt_or_ge 326254853756891 n with h12 | h12
            · -- n > 326254853756891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04203 n (by omega) (by omega)
            · -- n <= 326254853756891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04202 n (by omega) (by omega)
          · -- n <= 325333774467313
            exact RamareSaouter2003.prime_interval_nat_ladder_c04201 n (by omega) (by omega)
