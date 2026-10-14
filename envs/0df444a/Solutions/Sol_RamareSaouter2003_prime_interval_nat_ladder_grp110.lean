-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T16:50:17.757761+00:00
-- url     : https://prove2.me/submissions/60d67d86-295f-4cf8-99bf-f5f374a93761

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05500

theorem solution (n : Nat)
    (hn : 11105084835698311 < n) (hupper : n <= 12791132576439523) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 11918327077845589 n with h2 | h2
  · -- n > 11918327077845589
    rcases Nat.lt_or_ge 12329575047798641 n with h4 | h4
    · -- n > 12329575047798641
      rcases Nat.lt_or_ge 12540491171345243 n with h6 | h6
      · -- n > 12540491171345243
        rcases Nat.lt_or_ge 12647299834427057 n with h8 | h8
        · -- n > 12647299834427057
          rcases Nat.lt_or_ge 12719009546562989 n with h10 | h10
          · -- n > 12719009546562989
            rcases Nat.lt_or_ge 12755019715422857 n with h12 | h12
            · -- n > 12755019715422857
              exact RamareSaouter2003.prime_interval_nat_ladder_c05500 n (by omega) (by omega)
            · -- n <= 12755019715422857
              exact RamareSaouter2003.prime_interval_nat_ladder_c05499 n (by omega) (by omega)
          · -- n <= 12719009546562989
            rcases Nat.lt_or_ge 12683107051351889 n with h12 | h12
            · -- n > 12683107051351889
              exact RamareSaouter2003.prime_interval_nat_ladder_c05498 n (by omega) (by omega)
            · -- n <= 12683107051351889
              exact RamareSaouter2003.prime_interval_nat_ladder_c05497 n (by omega) (by omega)
        · -- n <= 12647299834427057
          rcases Nat.lt_or_ge 12575993570650463 n with h10 | h10
          · -- n > 12575993570650463
            rcases Nat.lt_or_ge 12611593090518953 n with h12 | h12
            · -- n > 12611593090518953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05496 n (by omega) (by omega)
            · -- n <= 12611593090518953
              exact RamareSaouter2003.prime_interval_nat_ladder_c05495 n (by omega) (by omega)
          · -- n <= 12575993570650463
            exact RamareSaouter2003.prime_interval_nat_ladder_c05494 n (by omega) (by omega)
      · -- n <= 12540491171345243
        rcases Nat.lt_or_ge 12434589504165061 n with h8 | h8
        · -- n > 12434589504165061
          rcases Nat.lt_or_ge 12469788344770721 n with h10 | h10
          · -- n > 12469788344770721
            rcases Nat.lt_or_ge 12505091069916751 n with h12 | h12
            · -- n > 12505091069916751
              exact RamareSaouter2003.prime_interval_nat_ladder_c05493 n (by omega) (by omega)
            · -- n <= 12505091069916751
              exact RamareSaouter2003.prime_interval_nat_ladder_c05492 n (by omega) (by omega)
          · -- n <= 12469788344770721
            exact RamareSaouter2003.prime_interval_nat_ladder_c05491 n (by omega) (by omega)
        · -- n <= 12434589504165061
          rcases Nat.lt_or_ge 12364482490725713 n with h10 | h10
          · -- n > 12364482490725713
            rcases Nat.lt_or_ge 12399485610444817 n with h12 | h12
            · -- n > 12399485610444817
              exact RamareSaouter2003.prime_interval_nat_ladder_c05490 n (by omega) (by omega)
            · -- n <= 12399485610444817
              exact RamareSaouter2003.prime_interval_nat_ladder_c05489 n (by omega) (by omega)
          · -- n <= 12364482490725713
            exact RamareSaouter2003.prime_interval_nat_ladder_c05488 n (by omega) (by omega)
    · -- n <= 12329575047798641
      rcases Nat.lt_or_ge 12122209220682163 n with h6 | h6
      · -- n > 12122209220682163
        rcases Nat.lt_or_ge 12225447518006809 n with h8 | h8
        · -- n > 12225447518006809
          rcases Nat.lt_or_ge 12260056995160591 n with h10 | h10
          · -- n > 12260056995160591
            rcases Nat.lt_or_ge 12294768613154813 n with h12 | h12
            · -- n > 12294768613154813
              exact RamareSaouter2003.prime_interval_nat_ladder_c05487 n (by omega) (by omega)
            · -- n <= 12294768613154813
              exact RamareSaouter2003.prime_interval_nat_ladder_c05486 n (by omega) (by omega)
          · -- n <= 12260056995160591
            exact RamareSaouter2003.prime_interval_nat_ladder_c05485 n (by omega) (by omega)
        · -- n <= 12225447518006809
          rcases Nat.lt_or_ge 12156529249460551 n with h10 | h10
          · -- n > 12156529249460551
            rcases Nat.lt_or_ge 12190943055554077 n with h12 | h12
            · -- n > 12190943055554077
              exact RamareSaouter2003.prime_interval_nat_ladder_c05484 n (by omega) (by omega)
            · -- n <= 12190943055554077
              exact RamareSaouter2003.prime_interval_nat_ladder_c05483 n (by omega) (by omega)
          · -- n <= 12156529249460551
            exact RamareSaouter2003.prime_interval_nat_ladder_c05482 n (by omega) (by omega)
      · -- n <= 12122209220682163
        rcases Nat.lt_or_ge 12019834055951237 n with h8 | h8
        · -- n > 12019834055951237
          rcases Nat.lt_or_ge 12053864912572493 n with h10 | h10
          · -- n > 12053864912572493
            rcases Nat.lt_or_ge 12087992908706437 n with h12 | h12
            · -- n > 12087992908706437
              exact RamareSaouter2003.prime_interval_nat_ladder_c05481 n (by omega) (by omega)
            · -- n <= 12087992908706437
              exact RamareSaouter2003.prime_interval_nat_ladder_c05480 n (by omega) (by omega)
          · -- n <= 12053864912572493
            exact RamareSaouter2003.prime_interval_nat_ladder_c05479 n (by omega) (by omega)
        · -- n <= 12019834055951237
          rcases Nat.lt_or_ge 11952060974722801 n with h10 | h10
          · -- n > 11952060974722801
            rcases Nat.lt_or_ge 11985898605954817 n with h12 | h12
            · -- n > 11985898605954817
              exact RamareSaouter2003.prime_interval_nat_ladder_c05478 n (by omega) (by omega)
            · -- n <= 11985898605954817
              exact RamareSaouter2003.prime_interval_nat_ladder_c05477 n (by omega) (by omega)
          · -- n <= 11952060974722801
            exact RamareSaouter2003.prime_interval_nat_ladder_c05476 n (by omega) (by omega)
  · -- n <= 11918327077845589
    rcases Nat.lt_or_ge 11488268601564779 n with h4 | h4
    · -- n > 11488268601564779
      rcases Nat.lt_or_ge 11684788452337691 n with h6 | h6
      · -- n > 11684788452337691
        rcases Nat.lt_or_ge 11784310677314101 n with h8 | h8
        · -- n > 11784310677314101
          rcases Nat.lt_or_ge 11851131615092417 n with h10 | h10
          · -- n > 11851131615092417
            rcases Nat.lt_or_ge 11884683581065039 n with h12 | h12
            · -- n > 11884683581065039
              exact RamareSaouter2003.prime_interval_nat_ladder_c05475 n (by omega) (by omega)
            · -- n <= 11884683581065039
              exact RamareSaouter2003.prime_interval_nat_ladder_c05474 n (by omega) (by omega)
          · -- n <= 11851131615092417
            rcases Nat.lt_or_ge 11817675577259603 n with h12 | h12
            · -- n > 11817675577259603
              exact RamareSaouter2003.prime_interval_nat_ladder_c05473 n (by omega) (by omega)
            · -- n <= 11817675577259603
              exact RamareSaouter2003.prime_interval_nat_ladder_c05472 n (by omega) (by omega)
        · -- n <= 11784310677314101
          rcases Nat.lt_or_ge 11717867857324241 n with h10 | h10
          · -- n > 11717867857324241
            rcases Nat.lt_or_ge 11751042155252227 n with h12 | h12
            · -- n > 11751042155252227
              exact RamareSaouter2003.prime_interval_nat_ladder_c05471 n (by omega) (by omega)
            · -- n <= 11751042155252227
              exact RamareSaouter2003.prime_interval_nat_ladder_c05470 n (by omega) (by omega)
          · -- n <= 11717867857324241
            exact RamareSaouter2003.prime_interval_nat_ladder_c05469 n (by omega) (by omega)
      · -- n <= 11684788452337691
        rcases Nat.lt_or_ge 11586108261262621 n with h8 | h8
        · -- n > 11586108261262621
          rcases Nat.lt_or_ge 11618906151937753 n with h10 | h10
          · -- n > 11618906151937753
            rcases Nat.lt_or_ge 11651799192506411 n with h12 | h12
            · -- n > 11651799192506411
              exact RamareSaouter2003.prime_interval_nat_ladder_c05468 n (by omega) (by omega)
            · -- n <= 11651799192506411
              exact RamareSaouter2003.prime_interval_nat_ladder_c05467 n (by omega) (by omega)
          · -- n <= 11618906151937753
            exact RamareSaouter2003.prime_interval_nat_ladder_c05466 n (by omega) (by omega)
        · -- n <= 11586108261262621
          rcases Nat.lt_or_ge 11520788285753953 n with h10 | h10
          · -- n > 11520788285753953
            rcases Nat.lt_or_ge 11553402084369217 n with h12 | h12
            · -- n > 11553402084369217
              exact RamareSaouter2003.prime_interval_nat_ladder_c05465 n (by omega) (by omega)
            · -- n <= 11553402084369217
              exact RamareSaouter2003.prime_interval_nat_ladder_c05464 n (by omega) (by omega)
          · -- n <= 11520788285753953
            exact RamareSaouter2003.prime_interval_nat_ladder_c05463 n (by omega) (by omega)
    · -- n <= 11488268601564779
      rcases Nat.lt_or_ge 11295056903621003 n with h6 | h6
      · -- n > 11295056903621003
        rcases Nat.lt_or_ge 11391261550212667 n with h8 | h8
        · -- n > 11391261550212667
          rcases Nat.lt_or_ge 11423509275653333 n with h10 | h10
          · -- n > 11423509275653333
            rcases Nat.lt_or_ge 11455851191666023 n with h12 | h12
            · -- n > 11455851191666023
              exact RamareSaouter2003.prime_interval_nat_ladder_c05462 n (by omega) (by omega)
            · -- n <= 11455851191666023
              exact RamareSaouter2003.prime_interval_nat_ladder_c05461 n (by omega) (by omega)
          · -- n <= 11423509275653333
            exact RamareSaouter2003.prime_interval_nat_ladder_c05460 n (by omega) (by omega)
        · -- n <= 11391261550212667
          rcases Nat.lt_or_ge 11327033308903141 n with h10 | h10
          · -- n > 11327033308903141
            rcases Nat.lt_or_ge 11359103309327407 n with h12 | h12
            · -- n > 11359103309327407
              exact RamareSaouter2003.prime_interval_nat_ladder_c05459 n (by omega) (by omega)
            · -- n <= 11359103309327407
              exact RamareSaouter2003.prime_interval_nat_ladder_c05458 n (by omega) (by omega)
          · -- n <= 11327033308903141
            exact RamareSaouter2003.prime_interval_nat_ladder_c05457 n (by omega) (by omega)
      · -- n <= 11295056903621003
        rcases Nat.lt_or_ge 11199668295031847 n with h8 | h8
        · -- n > 11199668295031847
          rcases Nat.lt_or_ge 11231373839266729 n with h10 | h10
          · -- n > 11231373839266729
            rcases Nat.lt_or_ge 11263170046412971 n with h12 | h12
            · -- n > 11263170046412971
              exact RamareSaouter2003.prime_interval_nat_ladder_c05456 n (by omega) (by omega)
            · -- n <= 11263170046412971
              exact RamareSaouter2003.prime_interval_nat_ladder_c05455 n (by omega) (by omega)
          · -- n <= 11231373839266729
            exact RamareSaouter2003.prime_interval_nat_ladder_c05454 n (by omega) (by omega)
        · -- n <= 11199668295031847
          rcases Nat.lt_or_ge 11136525245967911 n with h10 | h10
          · -- n > 11136525245967911
            rcases Nat.lt_or_ge 11168052579606961 n with h12 | h12
            · -- n > 11168052579606961
              exact RamareSaouter2003.prime_interval_nat_ladder_c05453 n (by omega) (by omega)
            · -- n <= 11168052579606961
              exact RamareSaouter2003.prime_interval_nat_ladder_c05452 n (by omega) (by omega)
          · -- n <= 11136525245967911
            exact RamareSaouter2003.prime_interval_nat_ladder_c05451 n (by omega) (by omega)
