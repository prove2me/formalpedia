-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T11:03:42.727972+00:00
-- url     : https://prove2.me/submissions/80b6a437-df1c-4fba-ab25-408aba721919

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04500

theorem solution (n : Nat)
    (hn : 657550128634237 < n) (hupper : n <= 757347815694311) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 705689033366561 n with h2 | h2
  · -- n > 705689033366561
    rcases Nat.lt_or_ge 730032959953789 n with h4 | h4
    · -- n > 730032959953789
      rcases Nat.lt_or_ge 742513182508081 n with h6 | h6
      · -- n > 742513182508081
        rcases Nat.lt_or_ge 748835565324883 n with h8 | h8
        · -- n > 748835565324883
          rcases Nat.lt_or_ge 753078898831561 n with h10 | h10
          · -- n > 753078898831561
            rcases Nat.lt_or_ge 755210420666341 n with h12 | h12
            · -- n > 755210420666341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04500 n (by omega) (by omega)
            · -- n <= 755210420666341
              exact RamareSaouter2003.prime_interval_nat_ladder_c04499 n (by omega) (by omega)
          · -- n <= 753078898831561
            rcases Nat.lt_or_ge 750954884661019 n with h12 | h12
            · -- n > 750954884661019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04498 n (by omega) (by omega)
            · -- n <= 750954884661019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04497 n (by omega) (by omega)
        · -- n <= 748835565324883
          rcases Nat.lt_or_ge 744614972106727 n with h10 | h10
          · -- n > 744614972106727
            rcases Nat.lt_or_ge 746722904683451 n with h12 | h12
            · -- n > 746722904683451
              exact RamareSaouter2003.prime_interval_nat_ladder_c04496 n (by omega) (by omega)
            · -- n <= 746722904683451
              exact RamareSaouter2003.prime_interval_nat_ladder_c04495 n (by omega) (by omega)
          · -- n <= 744614972106727
            exact RamareSaouter2003.prime_interval_nat_ladder_c04494 n (by omega) (by omega)
      · -- n <= 742513182508081
        rcases Nat.lt_or_ge 736244518279859 n with h8 | h8
        · -- n > 736244518279859
          rcases Nat.lt_or_ge 738328240340419 n with h10 | h10
          · -- n > 738328240340419
            rcases Nat.lt_or_ge 740418226526029 n with h12 | h12
            · -- n > 740418226526029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04493 n (by omega) (by omega)
            · -- n <= 740418226526029
              exact RamareSaouter2003.prime_interval_nat_ladder_c04492 n (by omega) (by omega)
          · -- n <= 738328240340419
            exact RamareSaouter2003.prime_interval_nat_ladder_c04491 n (by omega) (by omega)
        · -- n <= 736244518279859
          rcases Nat.lt_or_ge 732099599166647 n with h10 | h10
          · -- n > 732099599166647
            rcases Nat.lt_or_ge 734168020977983 n with h12 | h12
            · -- n > 734168020977983
              exact RamareSaouter2003.prime_interval_nat_ladder_c04490 n (by omega) (by omega)
            · -- n <= 734168020977983
              exact RamareSaouter2003.prime_interval_nat_ladder_c04489 n (by omega) (by omega)
          · -- n <= 732099599166647
            exact RamareSaouter2003.prime_interval_nat_ladder_c04488 n (by omega) (by omega)
    · -- n <= 730032959953789
      rcases Nat.lt_or_ge 717757741525739 n with h6 | h6
      · -- n > 717757741525739
        rcases Nat.lt_or_ge 723869130630661 n with h8 | h8
        · -- n > 723869130630661
          rcases Nat.lt_or_ge 725918412262513 n with h10 | h10
          · -- n > 725918412262513
            rcases Nat.lt_or_ge 727972476713687 n with h12 | h12
            · -- n > 727972476713687
              exact RamareSaouter2003.prime_interval_nat_ladder_c04487 n (by omega) (by omega)
            · -- n <= 727972476713687
              exact RamareSaouter2003.prime_interval_nat_ladder_c04486 n (by omega) (by omega)
          · -- n <= 725918412262513
            exact RamareSaouter2003.prime_interval_nat_ladder_c04485 n (by omega) (by omega)
        · -- n <= 723869130630661
          rcases Nat.lt_or_ge 719789774861447 n with h10 | h10
          · -- n > 719789774861447
            rcases Nat.lt_or_ge 721826076828119 n with h12 | h12
            · -- n > 721826076828119
              exact RamareSaouter2003.prime_interval_nat_ladder_c04484 n (by omega) (by omega)
            · -- n <= 721826076828119
              exact RamareSaouter2003.prime_interval_nat_ladder_c04483 n (by omega) (by omega)
          · -- n <= 719789774861447
            exact RamareSaouter2003.prime_interval_nat_ladder_c04482 n (by omega) (by omega)
      · -- n <= 717757741525739
        rcases Nat.lt_or_ge 711698298050477 n with h8 | h8
        · -- n > 711698298050477
          rcases Nat.lt_or_ge 713712551592167 n with h10 | h10
          · -- n > 713712551592167
            rcases Nat.lt_or_ge 715731362558519 n with h12 | h12
            · -- n > 715731362558519
              exact RamareSaouter2003.prime_interval_nat_ladder_c04481 n (by omega) (by omega)
            · -- n <= 715731362558519
              exact RamareSaouter2003.prime_interval_nat_ladder_c04480 n (by omega) (by omega)
          · -- n <= 713712551592167
            exact RamareSaouter2003.prime_interval_nat_ladder_c04479 n (by omega) (by omega)
        · -- n <= 711698298050477
          rcases Nat.lt_or_ge 707685671291591 n with h10 | h10
          · -- n > 707685671291591
            rcases Nat.lt_or_ge 709689075577673 n with h12 | h12
            · -- n > 709689075577673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04478 n (by omega) (by omega)
            · -- n <= 709689075577673
              exact RamareSaouter2003.prime_interval_nat_ladder_c04477 n (by omega) (by omega)
          · -- n <= 707685671291591
            exact RamareSaouter2003.prime_interval_nat_ladder_c04476 n (by omega) (by omega)
  · -- n <= 705689033366561
    rcases Nat.lt_or_ge 680231144196589 n with h4 | h4
    · -- n > 680231144196589
      rcases Nat.lt_or_ge 691863758315633 n with h6 | h6
      · -- n > 691863758315633
        rcases Nat.lt_or_ge 697755509661011 n with h8 | h8
        · -- n > 697755509661011
          rcases Nat.lt_or_ge 701711473449989 n with h10 | h10
          · -- n > 701711473449989
            rcases Nat.lt_or_ge 703696963888949 n with h12 | h12
            · -- n > 703696963888949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04475 n (by omega) (by omega)
            · -- n <= 703696963888949
              exact RamareSaouter2003.prime_interval_nat_ladder_c04474 n (by omega) (by omega)
          · -- n <= 701711473449989
            rcases Nat.lt_or_ge 699730637849939 n with h12 | h12
            · -- n > 699730637849939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04473 n (by omega) (by omega)
            · -- n <= 699730637849939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04472 n (by omega) (by omega)
        · -- n <= 697755509661011
          rcases Nat.lt_or_ge 693822634969463 n with h10 | h10
          · -- n > 693822634969463
            rcases Nat.lt_or_ge 695786865731819 n with h12 | h12
            · -- n > 695786865731819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04471 n (by omega) (by omega)
            · -- n <= 695786865731819
              exact RamareSaouter2003.prime_interval_nat_ladder_c04470 n (by omega) (by omega)
          · -- n <= 693822634969463
            exact RamareSaouter2003.prime_interval_nat_ladder_c04469 n (by omega) (by omega)
      · -- n <= 691863758315633
        rcases Nat.lt_or_ge 686022970584613 n with h8 | h8
        · -- n > 686022970584613
          rcases Nat.lt_or_ge 687964858961377 n with h10 | h10
          · -- n > 687964858961377
            rcases Nat.lt_or_ge 689912433138697 n with h12 | h12
            · -- n > 689912433138697
              exact RamareSaouter2003.prime_interval_nat_ladder_c04468 n (by omega) (by omega)
            · -- n <= 689912433138697
              exact RamareSaouter2003.prime_interval_nat_ladder_c04467 n (by omega) (by omega)
          · -- n <= 687964858961377
            exact RamareSaouter2003.prime_interval_nat_ladder_c04466 n (by omega) (by omega)
        · -- n <= 686022970584613
          rcases Nat.lt_or_ge 682156831341329 n with h10 | h10
          · -- n > 682156831341329
            rcases Nat.lt_or_ge 684086284323671 n with h12 | h12
            · -- n > 684086284323671
              exact RamareSaouter2003.prime_interval_nat_ladder_c04465 n (by omega) (by omega)
            · -- n <= 684086284323671
              exact RamareSaouter2003.prime_interval_nat_ladder_c04464 n (by omega) (by omega)
          · -- n <= 682156831341329
            exact RamareSaouter2003.prime_interval_nat_ladder_c04463 n (by omega) (by omega)
    · -- n <= 680231144196589
      rcases Nat.lt_or_ge 668796093236429 n with h6 | h6
      · -- n > 668796093236429
        rcases Nat.lt_or_ge 674488438408487 n with h8 | h8
        · -- n > 674488438408487
          rcases Nat.lt_or_ge 676397142281239 n with h10 | h10
          · -- n > 676397142281239
            rcases Nat.lt_or_ge 678310991475517 n with h12 | h12
            · -- n > 678310991475517
              exact RamareSaouter2003.prime_interval_nat_ladder_c04462 n (by omega) (by omega)
            · -- n <= 678310991475517
              exact RamareSaouter2003.prime_interval_nat_ladder_c04461 n (by omega) (by omega)
          · -- n <= 676397142281239
            exact RamareSaouter2003.prime_interval_nat_ladder_c04460 n (by omega) (by omega)
        · -- n <= 674488438408487
          rcases Nat.lt_or_ge 670687820958679 n with h10 | h10
          · -- n > 670687820958679
            rcases Nat.lt_or_ge 672584661142799 n with h12 | h12
            · -- n > 672584661142799
              exact RamareSaouter2003.prime_interval_nat_ladder_c04459 n (by omega) (by omega)
            · -- n <= 672584661142799
              exact RamareSaouter2003.prime_interval_nat_ladder_c04458 n (by omega) (by omega)
          · -- n <= 670687820958679
            exact RamareSaouter2003.prime_interval_nat_ladder_c04457 n (by omega) (by omega)
      · -- n <= 668796093236429
        rcases Nat.lt_or_ge 663147852135959 n with h8 | h8
        · -- n > 663147852135959
          rcases Nat.lt_or_ge 665025393611309 n with h10 | h10
          · -- n > 665025393611309
            rcases Nat.lt_or_ge 666907964778689 n with h12 | h12
            · -- n > 666907964778689
              exact RamareSaouter2003.prime_interval_nat_ladder_c04456 n (by omega) (by omega)
            · -- n <= 666907964778689
              exact RamareSaouter2003.prime_interval_nat_ladder_c04455 n (by omega) (by omega)
          · -- n <= 665025393611309
            exact RamareSaouter2003.prime_interval_nat_ladder_c04454 n (by omega) (by omega)
        · -- n <= 663147852135959
          rcases Nat.lt_or_ge 659410747083917 n with h10 | h10
          · -- n > 659410747083917
            rcases Nat.lt_or_ge 661276718691749 n with h12 | h12
            · -- n > 661276718691749
              exact RamareSaouter2003.prime_interval_nat_ladder_c04453 n (by omega) (by omega)
            · -- n <= 661276718691749
              exact RamareSaouter2003.prime_interval_nat_ladder_c04452 n (by omega) (by omega)
          · -- n <= 659410747083917
            exact RamareSaouter2003.prime_interval_nat_ladder_c04451 n (by omega) (by omega)
