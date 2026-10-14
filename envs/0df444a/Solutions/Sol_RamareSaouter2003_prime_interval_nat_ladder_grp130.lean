-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T23:42:25.149987+00:00
-- url     : https://prove2.me/submissions/3218ec28-34de-495a-8e23-a7a8000b570b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06500

theorem solution (n : Nat)
    (hn : 187640393798056393 < n) (hupper : n <= 216131755642320989) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 201382975595920361 n with h2 | h2
  · -- n > 201382975595920361
    rcases Nat.lt_or_ge 208332233142178283 n with h4 | h4
    · -- n > 208332233142178283
      rcases Nat.lt_or_ge 211896398904699527 n with h6 | h6
      · -- n > 211896398904699527
        rcases Nat.lt_or_ge 213701270800357141 n with h8 | h8
        · -- n > 213701270800357141
          rcases Nat.lt_or_ge 214913081432330063 n with h10 | h10
          · -- n > 214913081432330063
            rcases Nat.lt_or_ge 215521557005137333 n with h12 | h12
            · -- n > 215521557005137333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06500 n (by omega) (by omega)
            · -- n <= 215521557005137333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06499 n (by omega) (by omega)
          · -- n <= 214913081432330063
            rcases Nat.lt_or_ge 214306316851910561 n with h12 | h12
            · -- n > 214306316851910561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06498 n (by omega) (by omega)
            · -- n <= 214306316851910561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06497 n (by omega) (by omega)
        · -- n <= 213701270800357141
          rcases Nat.lt_or_ge 212496339915390029 n with h10 | h10
          · -- n > 212496339915390029
            rcases Nat.lt_or_ge 213097938677822519 n with h12 | h12
            · -- n > 213097938677822519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06496 n (by omega) (by omega)
            · -- n <= 213097938677822519
              exact RamareSaouter2003.prime_interval_nat_ladder_c06495 n (by omega) (by omega)
          · -- n <= 212496339915390029
            exact RamareSaouter2003.prime_interval_nat_ladder_c06494 n (by omega) (by omega)
      · -- n <= 211896398904699527
        rcases Nat.lt_or_ge 210106780920656689 n with h8 | h8
        · -- n > 210106780920656689
          rcases Nat.lt_or_ge 210701640972729917 n with h10 | h10
          · -- n > 210701640972729917
            rcases Nat.lt_or_ge 211298165612973431 n with h12 | h12
            · -- n > 211298165612973431
              exact RamareSaouter2003.prime_interval_nat_ladder_c06493 n (by omega) (by omega)
            · -- n <= 211298165612973431
              exact RamareSaouter2003.prime_interval_nat_ladder_c06492 n (by omega) (by omega)
          · -- n <= 210701640972729917
            exact RamareSaouter2003.prime_interval_nat_ladder_c06491 n (by omega) (by omega)
        · -- n <= 210106780920656689
          rcases Nat.lt_or_ge 208922080155150463 n with h10 | h10
          · -- n > 208922080155150463
            rcases Nat.lt_or_ge 209513587553434189 n with h12 | h12
            · -- n > 209513587553434189
              exact RamareSaouter2003.prime_interval_nat_ladder_c06490 n (by omega) (by omega)
            · -- n <= 209513587553434189
              exact RamareSaouter2003.prime_interval_nat_ladder_c06489 n (by omega) (by omega)
          · -- n <= 208922080155150463
            exact RamareSaouter2003.prime_interval_nat_ladder_c06488 n (by omega) (by omega)
    · -- n <= 208332233142178283
      rcases Nat.lt_or_ge 204828043586010349 n with h6 | h6
      · -- n > 204828043586010349
        rcases Nat.lt_or_ge 206572717682477207 n with h8 | h8
        · -- n > 206572717682477207
          rcases Nat.lt_or_ge 207157579691268641 n with h10 | h10
          · -- n > 207157579691268641
            rcases Nat.lt_or_ge 207744089782895249 n with h12 | h12
            · -- n > 207744089782895249
              exact RamareSaouter2003.prime_interval_nat_ladder_c06487 n (by omega) (by omega)
            · -- n <= 207744089782895249
              exact RamareSaouter2003.prime_interval_nat_ladder_c06486 n (by omega) (by omega)
          · -- n <= 207157579691268641
            exact RamareSaouter2003.prime_interval_nat_ladder_c06485 n (by omega) (by omega)
        · -- n <= 206572717682477207
          rcases Nat.lt_or_ge 205407973094627101 n with h10 | h10
          · -- n > 205407973094627101
            rcases Nat.lt_or_ge 205989530275114643 n with h12 | h12
            · -- n > 205989530275114643
              exact RamareSaouter2003.prime_interval_nat_ladder_c06484 n (by omega) (by omega)
            · -- n <= 205989530275114643
              exact RamareSaouter2003.prime_interval_nat_ladder_c06483 n (by omega) (by omega)
          · -- n <= 205407973094627101
            exact RamareSaouter2003.prime_interval_nat_ladder_c06482 n (by omega) (by omega)
      · -- n <= 204828043586010349
        rcases Nat.lt_or_ge 203098197891841831 n with h8 | h8
        · -- n > 203098197891841831
          rcases Nat.lt_or_ge 203673184809847057 n with h10 | h10
          · -- n > 203673184809847057
            rcases Nat.lt_or_ge 204249751824926333 n with h12 | h12
            · -- n > 204249751824926333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06481 n (by omega) (by omega)
            · -- n <= 204249751824926333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06480 n (by omega) (by omega)
          · -- n <= 203673184809847057
            exact RamareSaouter2003.prime_interval_nat_ladder_c06479 n (by omega) (by omega)
        · -- n <= 203098197891841831
          rcases Nat.lt_or_ge 201953123255057479 n with h10 | h10
          · -- n > 201953123255057479
            rcases Nat.lt_or_ge 202524836488930451 n with h12 | h12
            · -- n > 202524836488930451
              exact RamareSaouter2003.prime_interval_nat_ladder_c06478 n (by omega) (by omega)
            · -- n <= 202524836488930451
              exact RamareSaouter2003.prime_interval_nat_ladder_c06477 n (by omega) (by omega)
          · -- n <= 201953123255057479
            exact RamareSaouter2003.prime_interval_nat_ladder_c06476 n (by omega) (by omega)
  · -- n <= 201382975595920361
    rcases Nat.lt_or_ge 194115601724530481 n with h4 | h4
    · -- n > 194115601724530481
      rcases Nat.lt_or_ge 197436599502432331 n with h6 | h6
      · -- n > 197436599502432331
        rcases Nat.lt_or_ge 199118338069226969 n with h8 | h8
        · -- n > 199118338069226969
          rcases Nat.lt_or_ge 200247459052523291 n with h10 | h10
          · -- n > 200247459052523291
            rcases Nat.lt_or_ge 200814413602066853 n with h12 | h12
            · -- n > 200814413602066853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06475 n (by omega) (by omega)
            · -- n <= 200814413602066853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06474 n (by omega) (by omega)
          · -- n <= 200247459052523291
            rcases Nat.lt_or_ge 199682101375108153 n with h12 | h12
            · -- n > 199682101375108153
              exact RamareSaouter2003.prime_interval_nat_ladder_c06473 n (by omega) (by omega)
            · -- n <= 199682101375108153
              exact RamareSaouter2003.prime_interval_nat_ladder_c06472 n (by omega) (by omega)
        · -- n <= 199118338069226969
          rcases Nat.lt_or_ge 197995602543580711 n with h10 | h10
          · -- n > 197995602543580711
            rcases Nat.lt_or_ge 198556187201469289 n with h12 | h12
            · -- n > 198556187201469289
              exact RamareSaouter2003.prime_interval_nat_ladder_c06471 n (by omega) (by omega)
            · -- n <= 198556187201469289
              exact RamareSaouter2003.prime_interval_nat_ladder_c06470 n (by omega) (by omega)
          · -- n <= 197995602543580711
            exact RamareSaouter2003.prime_interval_nat_ladder_c06469 n (by omega) (by omega)
      · -- n <= 197436599502432331
        rcases Nat.lt_or_ge 195769062503354953 n with h8 | h8
        · -- n > 195769062503354953
          rcases Nat.lt_or_ge 196323343473570361 n with h10 | h10
          · -- n > 196323343473570361
            rcases Nat.lt_or_ge 196879180021510219 n with h12 | h12
            · -- n > 196879180021510219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06468 n (by omega) (by omega)
            · -- n <= 196879180021510219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06467 n (by omega) (by omega)
          · -- n <= 196323343473570361
            exact RamareSaouter2003.prime_interval_nat_ladder_c06466 n (by omega) (by omega)
        · -- n <= 195769062503354953
          rcases Nat.lt_or_ge 194665198489602727 n with h10 | h10
          · -- n > 194665198489602727
            rcases Nat.lt_or_ge 195216354223229231 n with h12 | h12
            · -- n > 195216354223229231
              exact RamareSaouter2003.prime_interval_nat_ladder_c06465 n (by omega) (by omega)
            · -- n <= 195216354223229231
              exact RamareSaouter2003.prime_interval_nat_ladder_c06464 n (by omega) (by omega)
          · -- n <= 194665198489602727
            exact RamareSaouter2003.prime_interval_nat_ladder_c06463 n (by omega) (by omega)
    · -- n <= 194115601724530481
      rcases Nat.lt_or_ge 190850536254429193 n with h6 | h6
      · -- n > 190850536254429193
        rcases Nat.lt_or_ge 192476132259141097 n with h8 | h8
        · -- n > 192476132259141097
          rcases Nat.lt_or_ge 193021087722439927 n with h10 | h10
          · -- n > 193021087722439927
            rcases Nat.lt_or_ge 193567560614077399 n with h12 | h12
            · -- n > 193567560614077399
              exact RamareSaouter2003.prime_interval_nat_ladder_c06462 n (by omega) (by omega)
            · -- n <= 193567560614077399
              exact RamareSaouter2003.prime_interval_nat_ladder_c06461 n (by omega) (by omega)
          · -- n <= 193021087722439927
            exact RamareSaouter2003.prime_interval_nat_ladder_c06460 n (by omega) (by omega)
        · -- n <= 192476132259141097
          rcases Nat.lt_or_ge 191390884283382461 n with h10 | h10
          · -- n > 191390884283382461
            rcases Nat.lt_or_ge 191932712923512101 n with h12 | h12
            · -- n > 191932712923512101
              exact RamareSaouter2003.prime_interval_nat_ladder_c06459 n (by omega) (by omega)
            · -- n <= 191932712923512101
              exact RamareSaouter2003.prime_interval_nat_ladder_c06458 n (by omega) (by omega)
          · -- n <= 191390884283382461
            exact RamareSaouter2003.prime_interval_nat_ladder_c06457 n (by omega) (by omega)
      · -- n <= 190850536254429193
        rcases Nat.lt_or_ge 189238655020063321 n with h8 | h8
        · -- n > 189238655020063321
          rcases Nat.lt_or_ge 189774437066617801 n with h10 | h10
          · -- n > 189774437066617801
            rcases Nat.lt_or_ge 190311718105095607 n with h12 | h12
            · -- n > 190311718105095607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06456 n (by omega) (by omega)
            · -- n <= 190311718105095607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06455 n (by omega) (by omega)
          · -- n <= 189774437066617801
            exact RamareSaouter2003.prime_interval_nat_ladder_c06454 n (by omega) (by omega)
        · -- n <= 189238655020063321
          rcases Nat.lt_or_ge 188171654414400067 n with h10 | h10
          · -- n > 188171654414400067
            rcases Nat.lt_or_ge 188704420151992009 n with h12 | h12
            · -- n > 188704420151992009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06453 n (by omega) (by omega)
            · -- n <= 188704420151992009
              exact RamareSaouter2003.prime_interval_nat_ladder_c06452 n (by omega) (by omega)
          · -- n <= 188171654414400067
            exact RamareSaouter2003.prime_interval_nat_ladder_c06451 n (by omega) (by omega)
