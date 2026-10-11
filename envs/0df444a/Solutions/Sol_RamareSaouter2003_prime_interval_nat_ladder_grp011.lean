-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T20:18:03.881981+00:00
-- url     : https://prove2.me/submissions/7d2744dd-a598-44b2-a281-befab481eeda

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00550

theorem solution (n : Nat)
    (hn : 32276278889 < n) (hupper : n <= 36137549639) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 34151144473 n with h2 | h2
  · -- n > 34151144473
    rcases Nat.lt_or_ge 35090290531 n with h4 | h4
    · -- n > 35090290531
      rcases Nat.lt_or_ge 35569728329 n with h6 | h6
      · -- n > 35569728329
        rcases Nat.lt_or_ge 35811954499 n with h8 | h8
        · -- n > 35811954499
          rcases Nat.lt_or_ge 35974375357 n with h10 | h10
          · -- n > 35974375357
            rcases Nat.lt_or_ge 36055868119 n with h12 | h12
            · -- n > 36055868119
              exact RamareSaouter2003.prime_interval_nat_ladder_c00550 n (by omega) (by omega)
            · -- n <= 36055868119
              exact RamareSaouter2003.prime_interval_nat_ladder_c00549 n (by omega) (by omega)
          · -- n <= 35974375357
            rcases Nat.lt_or_ge 35893070957 n with h12 | h12
            · -- n > 35893070957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00548 n (by omega) (by omega)
            · -- n <= 35893070957
              exact RamareSaouter2003.prime_interval_nat_ladder_c00547 n (by omega) (by omega)
        · -- n <= 35811954499
          rcases Nat.lt_or_ge 35650283611 n with h10 | h10
          · -- n > 35650283611
            rcases Nat.lt_or_ge 35731025531 n with h12 | h12
            · -- n > 35731025531
              exact RamareSaouter2003.prime_interval_nat_ladder_c00546 n (by omega) (by omega)
            · -- n <= 35731025531
              exact RamareSaouter2003.prime_interval_nat_ladder_c00545 n (by omega) (by omega)
          · -- n <= 35650283611
            exact RamareSaouter2003.prime_interval_nat_ladder_c00544 n (by omega) (by omega)
      · -- n <= 35569728329
        rcases Nat.lt_or_ge 35329177523 n with h8 | h8
        · -- n > 35329177523
          rcases Nat.lt_or_ge 35409175693 n with h10 | h10
          · -- n > 35409175693
            rcases Nat.lt_or_ge 35489359163 n with h12 | h12
            · -- n > 35489359163
              exact RamareSaouter2003.prime_interval_nat_ladder_c00543 n (by omega) (by omega)
            · -- n <= 35489359163
              exact RamareSaouter2003.prime_interval_nat_ladder_c00542 n (by omega) (by omega)
          · -- n <= 35409175693
            exact RamareSaouter2003.prime_interval_nat_ladder_c00541 n (by omega) (by omega)
        · -- n <= 35329177523
          rcases Nat.lt_or_ge 35169735479 n with h10 | h10
          · -- n > 35169735479
            rcases Nat.lt_or_ge 35249364197 n with h12 | h12
            · -- n > 35249364197
              exact RamareSaouter2003.prime_interval_nat_ladder_c00540 n (by omega) (by omega)
            · -- n <= 35249364197
              exact RamareSaouter2003.prime_interval_nat_ladder_c00539 n (by omega) (by omega)
          · -- n <= 35169735479
            exact RamareSaouter2003.prime_interval_nat_ladder_c00538 n (by omega) (by omega)
    · -- n <= 35090290531
      rcases Nat.lt_or_ge 34617460271 n with h6 | h6
      · -- n > 34617460271
        rcases Nat.lt_or_ge 34853055287 n with h8 | h8
        · -- n > 34853055287
          rcases Nat.lt_or_ge 34931950883 n with h10 | h10
          · -- n > 34931950883
            rcases Nat.lt_or_ge 35011029149 n with h12 | h12
            · -- n > 35011029149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00537 n (by omega) (by omega)
            · -- n <= 35011029149
              exact RamareSaouter2003.prime_interval_nat_ladder_c00536 n (by omega) (by omega)
          · -- n <= 34931950883
            exact RamareSaouter2003.prime_interval_nat_ladder_c00535 n (by omega) (by omega)
        · -- n <= 34853055287
          rcases Nat.lt_or_ge 34695810379 n with h10 | h10
          · -- n > 34695810379
            rcases Nat.lt_or_ge 34774341947 n with h12 | h12
            · -- n > 34774341947
              exact RamareSaouter2003.prime_interval_nat_ladder_c00534 n (by omega) (by omega)
            · -- n <= 34774341947
              exact RamareSaouter2003.prime_interval_nat_ladder_c00533 n (by omega) (by omega)
          · -- n <= 34695810379
            exact RamareSaouter2003.prime_interval_nat_ladder_c00532 n (by omega) (by omega)
      · -- n <= 34617460271
        rcases Nat.lt_or_ge 34383493777 n with h8 | h8
        · -- n > 34383493777
          rcases Nat.lt_or_ge 34461302357 n with h10 | h10
          · -- n > 34461302357
            rcases Nat.lt_or_ge 34539291047 n with h12 | h12
            · -- n > 34539291047
              exact RamareSaouter2003.prime_interval_nat_ladder_c00531 n (by omega) (by omega)
            · -- n <= 34539291047
              exact RamareSaouter2003.prime_interval_nat_ladder_c00530 n (by omega) (by omega)
          · -- n <= 34461302357
            exact RamareSaouter2003.prime_interval_nat_ladder_c00529 n (by omega) (by omega)
        · -- n <= 34383493777
          rcases Nat.lt_or_ge 34228415269 n with h10 | h10
          · -- n > 34228415269
            rcases Nat.lt_or_ge 34305864917 n with h12 | h12
            · -- n > 34305864917
              exact RamareSaouter2003.prime_interval_nat_ladder_c00528 n (by omega) (by omega)
            · -- n <= 34305864917
              exact RamareSaouter2003.prime_interval_nat_ladder_c00527 n (by omega) (by omega)
          · -- n <= 34228415269
            exact RamareSaouter2003.prime_interval_nat_ladder_c00526 n (by omega) (by omega)
  · -- n <= 34151144473
    rcases Nat.lt_or_ge 33162707351 n with h4 | h4
    · -- n > 33162707351
      rcases Nat.lt_or_ge 33615220937 n with h6 | h6
      · -- n > 33615220937
        rcases Nat.lt_or_ge 33843841159 n with h8 | h8
        · -- n > 33843841159
          rcases Nat.lt_or_ge 33997137709 n with h10 | h10
          · -- n > 33997137709
            rcases Nat.lt_or_ge 34074052123 n with h12 | h12
            · -- n > 34074052123
              exact RamareSaouter2003.prime_interval_nat_ladder_c00525 n (by omega) (by omega)
            · -- n <= 34074052123
              exact RamareSaouter2003.prime_interval_nat_ladder_c00524 n (by omega) (by omega)
          · -- n <= 33997137709
            rcases Nat.lt_or_ge 33920400859 n with h12 | h12
            · -- n > 33920400859
              exact RamareSaouter2003.prime_interval_nat_ladder_c00523 n (by omega) (by omega)
            · -- n <= 33920400859
              exact RamareSaouter2003.prime_interval_nat_ladder_c00522 n (by omega) (by omega)
        · -- n <= 33843841159
          rcases Nat.lt_or_ge 33691251623 n with h10 | h10
          · -- n > 33691251623
            rcases Nat.lt_or_ge 33767458199 n with h12 | h12
            · -- n > 33767458199
              exact RamareSaouter2003.prime_interval_nat_ladder_c00521 n (by omega) (by omega)
            · -- n <= 33767458199
              exact RamareSaouter2003.prime_interval_nat_ladder_c00520 n (by omega) (by omega)
          · -- n <= 33691251623
            exact RamareSaouter2003.prime_interval_nat_ladder_c00519 n (by omega) (by omega)
      · -- n <= 33615220937
        rcases Nat.lt_or_ge 33388180087 n with h8 | h8
        · -- n > 33388180087
          rcases Nat.lt_or_ge 33463685611 n with h10 | h10
          · -- n > 33463685611
            rcases Nat.lt_or_ge 33539365787 n with h12 | h12
            · -- n > 33539365787
              exact RamareSaouter2003.prime_interval_nat_ladder_c00518 n (by omega) (by omega)
            · -- n <= 33539365787
              exact RamareSaouter2003.prime_interval_nat_ladder_c00517 n (by omega) (by omega)
          · -- n <= 33463685611
            exact RamareSaouter2003.prime_interval_nat_ladder_c00516 n (by omega) (by omega)
        · -- n <= 33388180087
          rcases Nat.lt_or_ge 33237691373 n with h10 | h10
          · -- n > 33237691373
            rcases Nat.lt_or_ge 33312848791 n with h12 | h12
            · -- n > 33312848791
              exact RamareSaouter2003.prime_interval_nat_ladder_c00515 n (by omega) (by omega)
            · -- n <= 33312848791
              exact RamareSaouter2003.prime_interval_nat_ladder_c00514 n (by omega) (by omega)
          · -- n <= 33237691373
            exact RamareSaouter2003.prime_interval_nat_ladder_c00513 n (by omega) (by omega)
    · -- n <= 33162707351
      rcases Nat.lt_or_ge 32716422679 n with h6 | h6
      · -- n > 32716422679
        rcases Nat.lt_or_ge 32938791971 n with h8 | h8
        · -- n > 32938791971
          rcases Nat.lt_or_ge 33013258039 n with h10 | h10
          · -- n > 33013258039
            rcases Nat.lt_or_ge 33087896371 n with h12 | h12
            · -- n > 33087896371
              exact RamareSaouter2003.prime_interval_nat_ladder_c00512 n (by omega) (by omega)
            · -- n <= 33087896371
              exact RamareSaouter2003.prime_interval_nat_ladder_c00511 n (by omega) (by omega)
          · -- n <= 33013258039
            exact RamareSaouter2003.prime_interval_nat_ladder_c00510 n (by omega) (by omega)
        · -- n <= 32938791971
          rcases Nat.lt_or_ge 32790374581 n with h10 | h10
          · -- n > 32790374581
            rcases Nat.lt_or_ge 32864497579 n with h12 | h12
            · -- n > 32864497579
              exact RamareSaouter2003.prime_interval_nat_ladder_c00509 n (by omega) (by omega)
            · -- n <= 32864497579
              exact RamareSaouter2003.prime_interval_nat_ladder_c00508 n (by omega) (by omega)
          · -- n <= 32790374581
            exact RamareSaouter2003.prime_interval_nat_ladder_c00507 n (by omega) (by omega)
      · -- n <= 32716422679
        rcases Nat.lt_or_ge 32495588569 n with h8 | h8
        · -- n > 32495588569
          rcases Nat.lt_or_ge 32569030051 n with h10 | h10
          · -- n > 32569030051
            rcases Nat.lt_or_ge 32642641277 n with h12 | h12
            · -- n > 32642641277
              exact RamareSaouter2003.prime_interval_nat_ladder_c00506 n (by omega) (by omega)
            · -- n <= 32642641277
              exact RamareSaouter2003.prime_interval_nat_ladder_c00505 n (by omega) (by omega)
          · -- n <= 32569030051
            exact RamareSaouter2003.prime_interval_nat_ladder_c00504 n (by omega) (by omega)
        · -- n <= 32495588569
          rcases Nat.lt_or_ge 32349213373 n with h10 | h10
          · -- n > 32349213373
            rcases Nat.lt_or_ge 32422316483 n with h12 | h12
            · -- n > 32422316483
              exact RamareSaouter2003.prime_interval_nat_ladder_c00503 n (by omega) (by omega)
            · -- n <= 32422316483
              exact RamareSaouter2003.prime_interval_nat_ladder_c00502 n (by omega) (by omega)
          · -- n <= 32349213373
            exact RamareSaouter2003.prime_interval_nat_ladder_c00501 n (by omega) (by omega)
