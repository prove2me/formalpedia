-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T15:30:54.426524+00:00
-- url     : https://prove2.me/submissions/8bd6fe88-97d8-49e9-bbf0-c8fcbd749d87

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08500
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08521

theorem solution (n : Nat)
    (hn : 48896242901857136909 < n) (hupper : n <= 55110872013924363761) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 51847302069562391341 n with h2 | h2
  · -- n > 51847302069562391341
    rcases Nat.lt_or_ge 53388964626963715667 n with h4 | h4
    · -- n > 53388964626963715667
      rcases Nat.lt_or_ge 54176902209817424813 n with h6 | h6
      · -- n > 54176902209817424813
        rcases Nat.lt_or_ge 54575220978557534513 n with h8 | h8
        · -- n > 54575220978557534513
          rcases Nat.lt_or_ge 54842392312872998861 n with h10 | h10
          · -- n > 54842392312872998861
            rcases Nat.lt_or_ge 54976468211669375611 n with h12 | h12
            · -- n > 54976468211669375611
              exact RamareSaouter2003.prime_interval_nat_ladder_c08521 n (by omega) (by omega)
            · -- n <= 54976468211669375611
              exact RamareSaouter2003.prime_interval_nat_ladder_c08520 n (by omega) (by omega)
          · -- n <= 54842392312872998861
            rcases Nat.lt_or_ge 54708643745038609847 n with h12 | h12
            · -- n > 54708643745038609847
              exact RamareSaouter2003.prime_interval_nat_ladder_c08519 n (by omega) (by omega)
            · -- n <= 54708643745038609847
              exact RamareSaouter2003.prime_interval_nat_ladder_c08518 n (by omega) (by omega)
        · -- n <= 54575220978557534513
          rcases Nat.lt_or_ge 54309351307103575429 n with h10 | h10
          · -- n > 54309351307103575429
            rcases Nat.lt_or_ge 54442123579045393409 n with h12 | h12
            · -- n > 54442123579045393409
              exact RamareSaouter2003.prime_interval_nat_ladder_c08517 n (by omega) (by omega)
            · -- n <= 54442123579045393409
              exact RamareSaouter2003.prime_interval_nat_ladder_c08516 n (by omega) (by omega)
          · -- n <= 54309351307103575429
            exact RamareSaouter2003.prime_interval_nat_ladder_c08515 n (by omega) (by omega)
      · -- n <= 54176902209817424813
        rcases Nat.lt_or_ge 53781490082572265953 n with h8 | h8
        · -- n > 53781490082572265953
          rcases Nat.lt_or_ge 53912972475172460789 n with h10 | h10
          · -- n > 53912972475172460789
            rcases Nat.lt_or_ge 54044776095275974067 n with h12 | h12
            · -- n > 54044776095275974067
              exact RamareSaouter2003.prime_interval_nat_ladder_c08514 n (by omega) (by omega)
            · -- n <= 54044776095275974067
              exact RamareSaouter2003.prime_interval_nat_ladder_c08513 n (by omega) (by omega)
          · -- n <= 53912972475172460789
            exact RamareSaouter2003.prime_interval_nat_ladder_c08512 n (by omega) (by omega)
        · -- n <= 53781490082572265953
          rcases Nat.lt_or_ge 53519486752827079847 n with h10 | h10
          · -- n > 53519486752827079847
            rcases Nat.lt_or_ge 53650328595851500063 n with h12 | h12
            · -- n > 53650328595851500063
              exact RamareSaouter2003.prime_interval_nat_ladder_c08511 n (by omega) (by omega)
            · -- n <= 53650328595851500063
              exact RamareSaouter2003.prime_interval_nat_ladder_c08510 n (by omega) (by omega)
          · -- n <= 53519486752827079847
            exact RamareSaouter2003.prime_interval_nat_ladder_c08509 n (by omega) (by omega)
    · -- n <= 53388964626963715667
      rcases Nat.lt_or_ge 52612487487961421021 n with h6 | h6
      · -- n > 52612487487961421021
        rcases Nat.lt_or_ge 52999304068585937303 n with h8 | h8
        · -- n > 52999304068585937303
          rcases Nat.lt_or_ge 53128873815575683639 n with h10 | h10
          · -- n > 53128873815575683639
            rcases Nat.lt_or_ge 53258760640487262379 n with h12 | h12
            · -- n > 53258760640487262379
              exact RamareSaouter2003.prime_interval_nat_ladder_c08508 n (by omega) (by omega)
            · -- n <= 53258760640487262379
              exact RamareSaouter2003.prime_interval_nat_ladder_c08507 n (by omega) (by omega)
          · -- n <= 53128873815575683639
            exact RamareSaouter2003.prime_interval_nat_ladder_c08506 n (by omega) (by omega)
        · -- n <= 52999304068585937303
          rcases Nat.lt_or_ge 52741111830376785667 n with h10 | h10
          · -- n > 52741111830376785667
            rcases Nat.lt_or_ge 52870050412170411331 n with h12 | h12
            · -- n > 52870050412170411331
              exact RamareSaouter2003.prime_interval_nat_ladder_c08505 n (by omega) (by omega)
            · -- n <= 52870050412170411331
              exact RamareSaouter2003.prime_interval_nat_ladder_c08504 n (by omega) (by omega)
          · -- n <= 52741111830376785667
            exact RamareSaouter2003.prime_interval_nat_ladder_c08503 n (by omega) (by omega)
      · -- n <= 52612487487961421021
        rcases Nat.lt_or_ge 52228493173226679653 n with h8 | h8
        · -- n > 52228493173226679653
          rcases Nat.lt_or_ge 52356178884392190581 n with h10 | h10
          · -- n > 52356178884392190581
            rcases Nat.lt_or_ge 52484176633890458629 n with h12 | h12
            · -- n > 52484176633890458629
              exact RamareSaouter2003.prime_interval_nat_ladder_c08502 n (by omega) (by omega)
            · -- n <= 52484176633890458629
              exact RamareSaouter2003.prime_interval_nat_ladder_c08501 n (by omega) (by omega)
          · -- n <= 52356178884392190581
            exact RamareSaouter2003.prime_interval_nat_ladder_c08500 n (by omega) (by omega)
        · -- n <= 52228493173226679653
          rcases Nat.lt_or_ge 51974055198947864557 n with h10 | h10
          · -- n > 51974055198947864557
            rcases Nat.lt_or_ge 52101118903274447423 n with h12 | h12
            · -- n > 52101118903274447423
              exact RamareSaouter2003.prime_interval_nat_ladder_c08499 n (by omega) (by omega)
            · -- n <= 52101118903274447423
              exact RamareSaouter2003.prime_interval_nat_ladder_c08498 n (by omega) (by omega)
          · -- n <= 51974055198947864557
            exact RamareSaouter2003.prime_interval_nat_ladder_c08497 n (by omega) (by omega)
  · -- n <= 51847302069562391341
    rcases Nat.lt_or_ge 50350156469395812847 n with h4 | h4
    · -- n > 50350156469395812847
      rcases Nat.lt_or_ge 51093245483077185419 n with h6 | h6
      · -- n > 51093245483077185419
        rcases Nat.lt_or_ge 51468892758468477821 n with h8 | h8
        · -- n > 51468892758468477821
          rcases Nat.lt_or_ge 51594721376841147823 n with h10 | h10
          · -- n > 51594721376841147823
            rcases Nat.lt_or_ge 51720857419622744447 n with h12 | h12
            · -- n > 51720857419622744447
              exact RamareSaouter2003.prime_interval_nat_ladder_c08496 n (by omega) (by omega)
            · -- n <= 51720857419622744447
              exact RamareSaouter2003.prime_interval_nat_ladder_c08495 n (by omega) (by omega)
          · -- n <= 51594721376841147823
            exact RamareSaouter2003.prime_interval_nat_ladder_c08494 n (by omega) (by omega)
        · -- n <= 51468892758468477821
          rcases Nat.lt_or_ge 51218155487217871717 n with h10 | h10
          · -- n > 51218155487217871717
            rcases Nat.lt_or_ge 51343371058746356503 n with h12 | h12
            · -- n > 51343371058746356503
              exact RamareSaouter2003.prime_interval_nat_ladder_c08493 n (by omega) (by omega)
            · -- n <= 51343371058746356503
              exact RamareSaouter2003.prime_interval_nat_ladder_c08492 n (by omega) (by omega)
          · -- n <= 51218155487217871717
            exact RamareSaouter2003.prime_interval_nat_ladder_c08491 n (by omega) (by omega)
      · -- n <= 51093245483077185419
        rcases Nat.lt_or_ge 50720339997873544021 n with h8 | h8
        · -- n > 50720339997873544021
          rcases Nat.lt_or_ge 50844338702339876389 n with h10 | h10
          · -- n > 50844338702339876389
            rcases Nat.lt_or_ge 50968640531773895699 n with h12 | h12
            · -- n > 50968640531773895699
              exact RamareSaouter2003.prime_interval_nat_ladder_c08490 n (by omega) (by omega)
            · -- n <= 50968640531773895699
              exact RamareSaouter2003.prime_interval_nat_ladder_c08489 n (by omega) (by omega)
          · -- n <= 50844338702339876389
            exact RamareSaouter2003.prime_interval_nat_ladder_c08488 n (by omega) (by omega)
        · -- n <= 50720339997873544021
          rcases Nat.lt_or_ge 50473250131709927849 n with h10 | h10
          · -- n > 50473250131709927849
            rcases Nat.lt_or_ge 50596644633030205807 n with h12 | h12
            · -- n > 50596644633030205807
              exact RamareSaouter2003.prime_interval_nat_ladder_c08487 n (by omega) (by omega)
            · -- n <= 50596644633030205807
              exact RamareSaouter2003.prime_interval_nat_ladder_c08486 n (by omega) (by omega)
          · -- n <= 50473250131709927849
            exact RamareSaouter2003.prime_interval_nat_ladder_c08485 n (by omega) (by omega)
    · -- n <= 50350156469395812847
      rcases Nat.lt_or_ge 49617874447519134529 n with h6 | h6
      · -- n > 49617874447519134529
        rcases Nat.lt_or_ge 49982674835969540069 n with h8 | h8
        · -- n > 49982674835969540069
          rcases Nat.lt_or_ge 50104870029270069667 n with h10 | h10
          · -- n > 50104870029270069667
            rcases Nat.lt_or_ge 50227363507275331129 n with h12 | h12
            · -- n > 50227363507275331129
              exact RamareSaouter2003.prime_interval_nat_ladder_c08484 n (by omega) (by omega)
            · -- n <= 50227363507275331129
              exact RamareSaouter2003.prime_interval_nat_ladder_c08483 n (by omega) (by omega)
          · -- n <= 50104870029270069667
            exact RamareSaouter2003.prime_interval_nat_ladder_c08482 n (by omega) (by omega)
        · -- n <= 49982674835969540069
          rcases Nat.lt_or_ge 49739177617854836339 n with h10 | h10
          · -- n > 49739177617854836339
            rcases Nat.lt_or_ge 49860777636861248347 n with h12 | h12
            · -- n > 49860777636861248347
              exact RamareSaouter2003.prime_interval_nat_ladder_c08481 n (by omega) (by omega)
            · -- n <= 49860777636861248347
              exact RamareSaouter2003.prime_interval_nat_ladder_c08480 n (by omega) (by omega)
          · -- n <= 49739177617854836339
            exact RamareSaouter2003.prime_interval_nat_ladder_c08479 n (by omega) (by omega)
      · -- n <= 49617874447519134529
        rcases Nat.lt_or_ge 49255736968752405079 n with h8 | h8
        · -- n > 49255736968752405079
          rcases Nat.lt_or_ge 49376154958872135703 n with h10 | h10
          · -- n > 49376154958872135703
            rcases Nat.lt_or_ge 49496867201234538497 n with h12 | h12
            · -- n > 49496867201234538497
              exact RamareSaouter2003.prime_interval_nat_ladder_c08478 n (by omega) (by omega)
            · -- n <= 49496867201234538497
              exact RamareSaouter2003.prime_interval_nat_ladder_c08477 n (by omega) (by omega)
          · -- n <= 49376154958872135703
            exact RamareSaouter2003.prime_interval_nat_ladder_c08476 n (by omega) (by omega)
        · -- n <= 49255736968752405079
          rcases Nat.lt_or_ge 49015781891644901023 n with h10 | h10
          · -- n > 49015781891644901023
            rcases Nat.lt_or_ge 49135613003494092701 n with h12 | h12
            · -- n > 49135613003494092701
              exact RamareSaouter2003.prime_interval_nat_ladder_c08475 n (by omega) (by omega)
            · -- n <= 49135613003494092701
              exact RamareSaouter2003.prime_interval_nat_ladder_c08474 n (by omega) (by omega)
          · -- n <= 49015781891644901023
            exact RamareSaouter2003.prime_interval_nat_ladder_c08473 n (by omega) (by omega)
