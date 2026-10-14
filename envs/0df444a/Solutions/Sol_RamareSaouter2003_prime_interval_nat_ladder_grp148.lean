-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T06:12:24.859211+00:00
-- url     : https://prove2.me/submissions/a15f36e4-1db5-40ac-a348-fc29071dda2c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07350
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07351
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07352
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07353
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07354
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07355
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07356
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07357
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07358
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07359
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07360
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07361
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07362
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07363
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07364
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07365
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07366
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07367
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07368
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07369
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07370
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07371
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07372
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07373
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07374
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07375
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07376
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07377
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07378
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07379
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07380
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07381
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07382
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07383
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07384
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07385
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07386
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07387
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07388
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07389
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07390
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07391
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07392
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07393
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07394

theorem solution (n : Nat)
    (hn : 2356479914408562661 < n) (hupper : n <= 2706634033163334233) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2521928192805883357 n with h2 | h2
  · -- n > 2521928192805883357
    rcases Nat.lt_or_ge 2608958383506453551 n with h4 | h4
    · -- n > 2608958383506453551
      rcases Nat.lt_or_ge 2653593687774023543 n with h6 | h6
      · -- n > 2653593687774023543
        rcases Nat.lt_or_ge 2676196725735503963 n with h8 | h8
        · -- n > 2676196725735503963
          rcases Nat.lt_or_ge 2691372280984476989 n with h10 | h10
          · -- n > 2691372280984476989
            rcases Nat.lt_or_ge 2698992364845077101 n with h12 | h12
            · -- n > 2698992364845077101
              exact RamareSaouter2003.prime_interval_nat_ladder_c07394 n (by omega) (by omega)
            · -- n <= 2698992364845077101
              exact RamareSaouter2003.prime_interval_nat_ladder_c07393 n (by omega) (by omega)
          · -- n <= 2691372280984476989
            rcases Nat.lt_or_ge 2683773853658221757 n with h12 | h12
            · -- n > 2683773853658221757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07392 n (by omega) (by omega)
            · -- n <= 2683773853658221757
              exact RamareSaouter2003.prime_interval_nat_ladder_c07391 n (by omega) (by omega)
        · -- n <= 2676196725735503963
          rcases Nat.lt_or_ge 2661106603175678657 n with h10 | h10
          · -- n > 2661106603175678657
            rcases Nat.lt_or_ge 2668641005984372149 n with h12 | h12
            · -- n > 2668641005984372149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07390 n (by omega) (by omega)
            · -- n <= 2668641005984372149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07389 n (by omega) (by omega)
          · -- n <= 2661106603175678657
            exact RamareSaouter2003.prime_interval_nat_ladder_c07388 n (by omega) (by omega)
      · -- n <= 2653593687774023543
        rcases Nat.lt_or_ge 2631181398649815497 n with h8 | h8
        · -- n > 2631181398649815497
          rcases Nat.lt_or_ge 2638630999904960443 n with h10 | h10
          · -- n > 2638630999904960443
            rcases Nat.lt_or_ge 2646101764150189613 n with h12 | h12
            · -- n > 2646101764150189613
              exact RamareSaouter2003.prime_interval_nat_ladder_c07387 n (by omega) (by omega)
            · -- n <= 2646101764150189613
              exact RamareSaouter2003.prime_interval_nat_ladder_c07386 n (by omega) (by omega)
          · -- n <= 2638630999904960443
            exact RamareSaouter2003.prime_interval_nat_ladder_c07385 n (by omega) (by omega)
        · -- n <= 2631181398649815497
          rcases Nat.lt_or_ge 2616345120203510837 n with h10 | h10
          · -- n > 2616345120203510837
            rcases Nat.lt_or_ge 2623752772816200631 n with h12 | h12
            · -- n > 2623752772816200631
              exact RamareSaouter2003.prime_interval_nat_ladder_c07384 n (by omega) (by omega)
            · -- n <= 2623752772816200631
              exact RamareSaouter2003.prime_interval_nat_ladder_c07383 n (by omega) (by omega)
          · -- n <= 2616345120203510837
            exact RamareSaouter2003.prime_interval_nat_ladder_c07382 n (by omega) (by omega)
    · -- n <= 2608958383506453551
      rcases Nat.lt_or_ge 2565074222233514009 n with h6 | h6
      · -- n > 2565074222233514009
        rcases Nat.lt_or_ge 2586923090550833473 n with h8 | h8
        · -- n > 2586923090550833473
          rcases Nat.lt_or_ge 2594247461239124297 n with h10 | h10
          · -- n > 2594247461239124297
            rcases Nat.lt_or_ge 2601592566816586289 n with h12 | h12
            · -- n > 2601592566816586289
              exact RamareSaouter2003.prime_interval_nat_ladder_c07381 n (by omega) (by omega)
            · -- n <= 2601592566816586289
              exact RamareSaouter2003.prime_interval_nat_ladder_c07380 n (by omega) (by omega)
          · -- n <= 2594247461239124297
            exact RamareSaouter2003.prime_interval_nat_ladder_c07379 n (by omega) (by omega)
        · -- n <= 2586923090550833473
          rcases Nat.lt_or_ge 2572336523088272669 n with h10 | h10
          · -- n > 2572336523088272669
            rcases Nat.lt_or_ge 2579619523552288169 n with h12 | h12
            · -- n > 2579619523552288169
              exact RamareSaouter2003.prime_interval_nat_ladder_c07378 n (by omega) (by omega)
            · -- n <= 2579619523552288169
              exact RamareSaouter2003.prime_interval_nat_ladder_c07377 n (by omega) (by omega)
          · -- n <= 2572336523088272669
            exact RamareSaouter2003.prime_interval_nat_ladder_c07376 n (by omega) (by omega)
      · -- n <= 2565074222233514009
        rcases Nat.lt_or_ge 2543409635913829013 n with h8 | h8
        · -- n > 2543409635913829013
          rcases Nat.lt_or_ge 2550610772351792219 n with h10 | h10
          · -- n > 2550610772351792219
            rcases Nat.lt_or_ge 2557832224743977561 n with h12 | h12
            · -- n > 2557832224743977561
              exact RamareSaouter2003.prime_interval_nat_ladder_c07375 n (by omega) (by omega)
            · -- n <= 2557832224743977561
              exact RamareSaouter2003.prime_interval_nat_ladder_c07374 n (by omega) (by omega)
          · -- n <= 2550610772351792219
            exact RamareSaouter2003.prime_interval_nat_ladder_c07373 n (by omega) (by omega)
        · -- n <= 2543409635913829013
          rcases Nat.lt_or_ge 2529068402331548683 n with h10 | h10
          · -- n > 2529068402331548683
            rcases Nat.lt_or_ge 2536228964717253739 n with h12 | h12
            · -- n > 2536228964717253739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07372 n (by omega) (by omega)
            · -- n <= 2536228964717253739
              exact RamareSaouter2003.prime_interval_nat_ladder_c07371 n (by omega) (by omega)
          · -- n <= 2529068402331548683
            exact RamareSaouter2003.prime_interval_nat_ladder_c07370 n (by omega) (by omega)
  · -- n <= 2521928192805883357
    rcases Nat.lt_or_ge 2437800661926544939 n with h4 | h4
    · -- n > 2437800661926544939
      rcases Nat.lt_or_ge 2479507716441057641 n with h6 | h6
      · -- n > 2479507716441057641
        rcases Nat.lt_or_ge 2500627931488897549 n with h8 | h8
        · -- n > 2500627931488897549
          rcases Nat.lt_or_ge 2507707955542534061 n with h10 | h10
          · -- n > 2507707955542534061
            rcases Nat.lt_or_ge 2514808013626958521 n with h12 | h12
            · -- n > 2514808013626958521
              exact RamareSaouter2003.prime_interval_nat_ladder_c07369 n (by omega) (by omega)
            · -- n <= 2514808013626958521
              exact RamareSaouter2003.prime_interval_nat_ladder_c07368 n (by omega) (by omega)
          · -- n <= 2507707955542534061
            exact RamareSaouter2003.prime_interval_nat_ladder_c07367 n (by omega) (by omega)
        · -- n <= 2500627931488897549
          rcases Nat.lt_or_ge 2486527936087429873 n with h10 | h10
          · -- n > 2486527936087429873
            rcases Nat.lt_or_ge 2493567987806616143 n with h12 | h12
            · -- n > 2493567987806616143
              exact RamareSaouter2003.prime_interval_nat_ladder_c07366 n (by omega) (by omega)
            · -- n <= 2493567987806616143
              exact RamareSaouter2003.prime_interval_nat_ladder_c07365 n (by omega) (by omega)
          · -- n <= 2486527936087429873
            exact RamareSaouter2003.prime_interval_nat_ladder_c07364 n (by omega) (by omega)
      · -- n <= 2479507716441057641
        rcases Nat.lt_or_ge 2458565719836039277 n with h8 | h8
        · -- n > 2458565719836039277
          rcases Nat.lt_or_ge 2465526659516979491 n with h10 | h10
          · -- n > 2465526659516979491
            rcases Nat.lt_or_ge 2472507323628606029 n with h12 | h12
            · -- n > 2472507323628606029
              exact RamareSaouter2003.prime_interval_nat_ladder_c07363 n (by omega) (by omega)
            · -- n <= 2472507323628606029
              exact RamareSaouter2003.prime_interval_nat_ladder_c07362 n (by omega) (by omega)
          · -- n <= 2465526659516979491
            exact RamareSaouter2003.prime_interval_nat_ladder_c07361 n (by omega) (by omega)
        · -- n <= 2458565719836039277
          rcases Nat.lt_or_ge 2444702762778354763 n with h10 | h10
          · -- n > 2444702762778354763
            rcases Nat.lt_or_ge 2451624450571614949 n with h12 | h12
            · -- n > 2451624450571614949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07360 n (by omega) (by omega)
            · -- n <= 2451624450571614949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07359 n (by omega) (by omega)
          · -- n <= 2444702762778354763
            exact RamareSaouter2003.prime_interval_nat_ladder_c07358 n (by omega) (by omega)
    · -- n <= 2437800661926544939
      rcases Nat.lt_or_ge 2396795438111256253 n with h6 | h6
      · -- n > 2396795438111256253
        rcases Nat.lt_or_ge 2417211163638604573 n with h8 | h8
        · -- n > 2417211163638604573
          rcases Nat.lt_or_ge 2424054914670059303 n with h10 | h10
          · -- n > 2424054914670059303
            rcases Nat.lt_or_ge 2430918022171794349 n with h12 | h12
            · -- n > 2430918022171794349
              exact RamareSaouter2003.prime_interval_nat_ladder_c07357 n (by omega) (by omega)
            · -- n <= 2430918022171794349
              exact RamareSaouter2003.prime_interval_nat_ladder_c07356 n (by omega) (by omega)
          · -- n <= 2424054914670059303
            exact RamareSaouter2003.prime_interval_nat_ladder_c07355 n (by omega) (by omega)
        · -- n <= 2417211163638604573
          rcases Nat.lt_or_ge 2403581485055693009 n with h10 | h10
          · -- n > 2403581485055693009
            rcases Nat.lt_or_ge 2410386644743487831 n with h12 | h12
            · -- n > 2410386644743487831
              exact RamareSaouter2003.prime_interval_nat_ladder_c07354 n (by omega) (by omega)
            · -- n <= 2410386644743487831
              exact RamareSaouter2003.prime_interval_nat_ladder_c07353 n (by omega) (by omega)
          · -- n <= 2403581485055693009
            exact RamareSaouter2003.prime_interval_nat_ladder_c07352 n (by omega) (by omega)
      · -- n <= 2396795438111256253
        rcases Nat.lt_or_ge 2376552287270969221 n with h8 | h8
        · -- n > 2376552287270969221
          rcases Nat.lt_or_ge 2383280995805184661 n with h10 | h10
          · -- n > 2383280995805184661
            rcases Nat.lt_or_ge 2390028755165427023 n with h12 | h12
            · -- n > 2390028755165427023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07351 n (by omega) (by omega)
            · -- n <= 2390028755165427023
              exact RamareSaouter2003.prime_interval_nat_ladder_c07350 n (by omega) (by omega)
          · -- n <= 2383280995805184661
            exact RamareSaouter2003.prime_interval_nat_ladder_c07349 n (by omega) (by omega)
        · -- n <= 2376552287270969221
          rcases Nat.lt_or_ge 2363151743543593381 n with h10 | h10
          · -- n > 2363151743543593381
            rcases Nat.lt_or_ge 2369842551980842361 n with h12 | h12
            · -- n > 2369842551980842361
              exact RamareSaouter2003.prime_interval_nat_ladder_c07348 n (by omega) (by omega)
            · -- n <= 2369842551980842361
              exact RamareSaouter2003.prime_interval_nat_ladder_c07347 n (by omega) (by omega)
          · -- n <= 2363151743543593381
            exact RamareSaouter2003.prime_interval_nat_ladder_c07346 n (by omega) (by omega)
