-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T09:58:18.149801+00:00
-- url     : https://prove2.me/submissions/db9f0fbd-6c02-4c45-9d74-1fb21fbe494b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04300

theorem solution (n : Nat)
    (hn : 373647047298709 < n) (hupper : n <= 430355186223233) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 401000664624257 n with h2 | h2
  · -- n > 401000664624257
    rcases Nat.lt_or_ge 414831712955981 n with h4 | h4
    · -- n > 414831712955981
      rcases Nat.lt_or_ge 421926268588907 n with h6 | h6
      · -- n > 421926268588907
        rcases Nat.lt_or_ge 425518464382153 n with h8 | h8
        · -- n > 425518464382153
          rcases Nat.lt_or_ge 427929912764929 n with h10 | h10
          · -- n > 427929912764929
            rcases Nat.lt_or_ge 429140677581271 n with h12 | h12
            · -- n > 429140677581271
              exact RamareSaouter2003.prime_interval_nat_ladder_c04300 n (by omega) (by omega)
            · -- n <= 429140677581271
              exact RamareSaouter2003.prime_interval_nat_ladder_c04299 n (by omega) (by omega)
          · -- n <= 427929912764929
            rcases Nat.lt_or_ge 426722510783939 n with h12 | h12
            · -- n > 426722510783939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04298 n (by omega) (by omega)
            · -- n <= 426722510783939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04297 n (by omega) (by omega)
        · -- n <= 425518464382153
          rcases Nat.lt_or_ge 423119876692829 n with h10 | h10
          · -- n > 423119876692829
            rcases Nat.lt_or_ge 424317808854553 n with h12 | h12
            · -- n > 424317808854553
              exact RamareSaouter2003.prime_interval_nat_ladder_c04296 n (by omega) (by omega)
            · -- n <= 424317808854553
              exact RamareSaouter2003.prime_interval_nat_ladder_c04295 n (by omega) (by omega)
          · -- n <= 423119876692829
            exact RamareSaouter2003.prime_interval_nat_ladder_c04294 n (by omega) (by omega)
      · -- n <= 421926268588907
        rcases Nat.lt_or_ge 418363413355271 n with h8 | h8
        · -- n > 418363413355271
          rcases Nat.lt_or_ge 419547796669387 n with h10 | h10
          · -- n > 419547796669387
            rcases Nat.lt_or_ge 420735248784451 n with h12 | h12
            · -- n > 420735248784451
              exact RamareSaouter2003.prime_interval_nat_ladder_c04293 n (by omega) (by omega)
            · -- n <= 420735248784451
              exact RamareSaouter2003.prime_interval_nat_ladder_c04292 n (by omega) (by omega)
          · -- n <= 419547796669387
            exact RamareSaouter2003.prime_interval_nat_ladder_c04291 n (by omega) (by omega)
        · -- n <= 418363413355271
          rcases Nat.lt_or_ge 416005337225701 n with h10 | h10
          · -- n > 416005337225701
            rcases Nat.lt_or_ge 417183073588507 n with h12 | h12
            · -- n > 417183073588507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04290 n (by omega) (by omega)
            · -- n <= 417183073588507
              exact RamareSaouter2003.prime_interval_nat_ladder_c04289 n (by omega) (by omega)
          · -- n <= 416005337225701
            exact RamareSaouter2003.prime_interval_nat_ladder_c04288 n (by omega) (by omega)
    · -- n <= 414831712955981
      rcases Nat.lt_or_ge 407857936167181 n with h6 | h6
      · -- n > 407857936167181
        rcases Nat.lt_or_ge 411329261576213 n with h8 | h8
        · -- n > 411329261576213
          rcases Nat.lt_or_ge 412493539196929 n with h10 | h10
          · -- n > 412493539196929
            rcases Nat.lt_or_ge 413661047948641 n with h12 | h12
            · -- n > 413661047948641
              exact RamareSaouter2003.prime_interval_nat_ladder_c04287 n (by omega) (by omega)
            · -- n <= 413661047948641
              exact RamareSaouter2003.prime_interval_nat_ladder_c04286 n (by omega) (by omega)
          · -- n <= 412493539196929
            exact RamareSaouter2003.prime_interval_nat_ladder_c04285 n (by omega) (by omega)
        · -- n <= 411329261576213
          rcases Nat.lt_or_ge 409011023191163 n with h10 | h10
          · -- n > 409011023191163
            rcases Nat.lt_or_ge 410168370719201 n with h12 | h12
            · -- n > 410168370719201
              exact RamareSaouter2003.prime_interval_nat_ladder_c04284 n (by omega) (by omega)
            · -- n <= 410168370719201
              exact RamareSaouter2003.prime_interval_nat_ladder_c04283 n (by omega) (by omega)
          · -- n <= 409011023191163
            exact RamareSaouter2003.prime_interval_nat_ladder_c04282 n (by omega) (by omega)
      · -- n <= 407857936167181
        rcases Nat.lt_or_ge 404414713137247 n with h8 | h8
        · -- n > 404414713137247
          rcases Nat.lt_or_ge 405558576261907 n with h10 | h10
          · -- n > 405558576261907
            rcases Nat.lt_or_ge 406706799180959 n with h12 | h12
            · -- n > 406706799180959
              exact RamareSaouter2003.prime_interval_nat_ladder_c04281 n (by omega) (by omega)
            · -- n <= 406706799180959
              exact RamareSaouter2003.prime_interval_nat_ladder_c04280 n (by omega) (by omega)
          · -- n <= 405558576261907
            exact RamareSaouter2003.prime_interval_nat_ladder_c04279 n (by omega) (by omega)
        · -- n <= 404414713137247
          rcases Nat.lt_or_ge 402135401596417 n with h10 | h10
          · -- n > 402135401596417
            rcases Nat.lt_or_ge 403273951385189 n with h12 | h12
            · -- n > 403273951385189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04278 n (by omega) (by omega)
            · -- n <= 403273951385189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04277 n (by omega) (by omega)
          · -- n <= 402135401596417
            exact RamareSaouter2003.prime_interval_nat_ladder_c04276 n (by omega) (by omega)
  · -- n <= 401000664624257
    rcases Nat.lt_or_ge 386534317580057 n with h4 | h4
    · -- n > 386534317580057
      rcases Nat.lt_or_ge 393144231201077 n with h6 | h6
      · -- n > 393144231201077
        rcases Nat.lt_or_ge 396492283859267 n with h8 | h8
        · -- n > 396492283859267
          rcases Nat.lt_or_ge 398740353090683 n with h10 | h10
          · -- n > 398740353090683
            rcases Nat.lt_or_ge 399868930612321 n with h12 | h12
            · -- n > 399868930612321
              exact RamareSaouter2003.prime_interval_nat_ladder_c04275 n (by omega) (by omega)
            · -- n <= 399868930612321
              exact RamareSaouter2003.prime_interval_nat_ladder_c04274 n (by omega) (by omega)
          · -- n <= 398740353090683
            rcases Nat.lt_or_ge 397614805509617 n with h12 | h12
            · -- n > 397614805509617
              exact RamareSaouter2003.prime_interval_nat_ladder_c04273 n (by omega) (by omega)
            · -- n <= 397614805509617
              exact RamareSaouter2003.prime_interval_nat_ladder_c04272 n (by omega) (by omega)
        · -- n <= 396492283859267
          rcases Nat.lt_or_ge 394256844580259 n with h10 | h10
          · -- n > 394256844580259
            rcases Nat.lt_or_ge 395373018820267 n with h12 | h12
            · -- n > 395373018820267
              exact RamareSaouter2003.prime_interval_nat_ladder_c04271 n (by omega) (by omega)
            · -- n <= 395373018820267
              exact RamareSaouter2003.prime_interval_nat_ladder_c04270 n (by omega) (by omega)
          · -- n <= 394256844580259
            exact RamareSaouter2003.prime_interval_nat_ladder_c04269 n (by omega) (by omega)
      · -- n <= 393144231201077
        rcases Nat.lt_or_ge 389824667806009 n with h8 | h8
        · -- n > 389824667806009
          rcases Nat.lt_or_ge 390927871838297 n with h10 | h10
          · -- n > 390927871838297
            rcases Nat.lt_or_ge 392034337942259 n with h12 | h12
            · -- n > 392034337942259
              exact RamareSaouter2003.prime_interval_nat_ladder_c04268 n (by omega) (by omega)
            · -- n <= 392034337942259
              exact RamareSaouter2003.prime_interval_nat_ladder_c04267 n (by omega) (by omega)
          · -- n <= 390927871838297
            exact RamareSaouter2003.prime_interval_nat_ladder_c04266 n (by omega) (by omega)
        · -- n <= 389824667806009
          rcases Nat.lt_or_ge 387628488877459 n with h10 | h10
          · -- n > 387628488877459
            rcases Nat.lt_or_ge 388725545350463 n with h12 | h12
            · -- n > 388725545350463
              exact RamareSaouter2003.prime_interval_nat_ladder_c04265 n (by omega) (by omega)
            · -- n <= 388725545350463
              exact RamareSaouter2003.prime_interval_nat_ladder_c04264 n (by omega) (by omega)
          · -- n <= 387628488877459
            exact RamareSaouter2003.prime_interval_nat_ladder_c04263 n (by omega) (by omega)
    · -- n <= 386534317580057
      rcases Nat.lt_or_ge 380036312430757 n with h6 | h6
      · -- n > 380036312430757
        rcases Nat.lt_or_ge 383270519880047 n with h8 | h8
        · -- n > 383270519880047
          rcases Nat.lt_or_ge 384355359600089 n with h10 | h10
          · -- n > 384355359600089
            rcases Nat.lt_or_ge 385443460530643 n with h12 | h12
            · -- n > 385443460530643
              exact RamareSaouter2003.prime_interval_nat_ladder_c04262 n (by omega) (by omega)
            · -- n <= 385443460530643
              exact RamareSaouter2003.prime_interval_nat_ladder_c04261 n (by omega) (by omega)
          · -- n <= 384355359600089
            exact RamareSaouter2003.prime_interval_nat_ladder_c04260 n (by omega) (by omega)
        · -- n <= 383270519880047
          rcases Nat.lt_or_ge 381111843939163 n with h10 | h10
          · -- n > 381111843939163
            rcases Nat.lt_or_ge 382189401558347 n with h12 | h12
            · -- n > 382189401558347
              exact RamareSaouter2003.prime_interval_nat_ladder_c04259 n (by omega) (by omega)
            · -- n <= 382189401558347
              exact RamareSaouter2003.prime_interval_nat_ladder_c04258 n (by omega) (by omega)
          · -- n <= 381111843939163
            exact RamareSaouter2003.prime_interval_nat_ladder_c04257 n (by omega) (by omega)
      · -- n <= 380036312430757
        rcases Nat.lt_or_ge 376827221340389 n with h8 | h8
        · -- n > 376827221340389
          rcases Nat.lt_or_ge 377893695866339 n with h10 | h10
          · -- n > 377893695866339
            rcases Nat.lt_or_ge 378963390489989 n with h12 | h12
            · -- n > 378963390489989
              exact RamareSaouter2003.prime_interval_nat_ladder_c04256 n (by omega) (by omega)
            · -- n <= 378963390489989
              exact RamareSaouter2003.prime_interval_nat_ladder_c04255 n (by omega) (by omega)
          · -- n <= 377893695866339
            exact RamareSaouter2003.prime_interval_nat_ladder_c04254 n (by omega) (by omega)
        · -- n <= 376827221340389
          rcases Nat.lt_or_ge 374703749487283 n with h10 | h10
          · -- n > 374703749487283
            rcases Nat.lt_or_ge 375763649628197 n with h12 | h12
            · -- n > 375763649628197
              exact RamareSaouter2003.prime_interval_nat_ladder_c04253 n (by omega) (by omega)
            · -- n <= 375763649628197
              exact RamareSaouter2003.prime_interval_nat_ladder_c04252 n (by omega) (by omega)
          · -- n <= 374703749487283
            exact RamareSaouter2003.prime_interval_nat_ladder_c04251 n (by omega) (by omega)
