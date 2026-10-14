-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:55:24.151074+00:00
-- url     : https://prove2.me/submissions/9fa62379-e733-447e-b46b-65ce9e48b322

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03650

theorem solution (n : Nat)
    (hn : 66860666865847 < n) (hupper : n <= 75655853035559) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 71122435181953 n with h2 | h2
  · -- n > 71122435181953
    rcases Nat.lt_or_ge 73263532847633 n with h4 | h4
    · -- n > 73263532847633
      rcases Nat.lt_or_ge 74358132919409 n with h6 | h6
      · -- n > 74358132919409
        rcases Nat.lt_or_ge 74911550506453 n with h8 | h8
        · -- n > 74911550506453
          rcases Nat.lt_or_ge 75282781934441 n with h10 | h10
          · -- n > 75282781934441
            rcases Nat.lt_or_ge 75469086957067 n with h12 | h12
            · -- n > 75469086957067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03650 n (by omega) (by omega)
            · -- n <= 75469086957067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03649 n (by omega) (by omega)
          · -- n <= 75282781934441
            rcases Nat.lt_or_ge 75096936829283 n with h12 | h12
            · -- n > 75096936829283
              exact RamareSaouter2003.prime_interval_nat_ladder_c03648 n (by omega) (by omega)
            · -- n <= 75096936829283
              exact RamareSaouter2003.prime_interval_nat_ladder_c03647 n (by omega) (by omega)
        · -- n <= 74911550506453
          rcases Nat.lt_or_ge 74542149679841 n with h10 | h10
          · -- n > 74542149679841
            rcases Nat.lt_or_ge 74726621833181 n with h12 | h12
            · -- n > 74726621833181
              exact RamareSaouter2003.prime_interval_nat_ladder_c03646 n (by omega) (by omega)
            · -- n <= 74726621833181
              exact RamareSaouter2003.prime_interval_nat_ladder_c03645 n (by omega) (by omega)
          · -- n <= 74542149679841
            exact RamareSaouter2003.prime_interval_nat_ladder_c03644 n (by omega) (by omega)
      · -- n <= 74358132919409
        rcases Nat.lt_or_ge 73808803767871 n with h8 | h8
        · -- n > 73808803767871
          rcases Nat.lt_or_ge 73991461083571 n with h10 | h10
          · -- n > 73991461083571
            rcases Nat.lt_or_ge 74174570427733 n with h12 | h12
            · -- n > 74174570427733
              exact RamareSaouter2003.prime_interval_nat_ladder_c03643 n (by omega) (by omega)
            · -- n <= 74174570427733
              exact RamareSaouter2003.prime_interval_nat_ladder_c03642 n (by omega) (by omega)
          · -- n <= 73991461083571
            exact RamareSaouter2003.prime_interval_nat_ladder_c03641 n (by omega) (by omega)
        · -- n <= 73808803767871
          rcases Nat.lt_or_ge 73444840761667 n with h10 | h10
          · -- n > 73444840761667
            rcases Nat.lt_or_ge 73626597364927 n with h12 | h12
            · -- n > 73626597364927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03640 n (by omega) (by omega)
            · -- n <= 73626597364927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03639 n (by omega) (by omega)
          · -- n <= 73444840761667
            exact RamareSaouter2003.prime_interval_nat_ladder_c03638 n (by omega) (by omega)
    · -- n <= 73263532847633
      rcases Nat.lt_or_ge 72185046001121 n with h6 | h6
      · -- n > 72185046001121
        rcases Nat.lt_or_ge 72722290178467 n with h8 | h8
        · -- n > 72722290178467
          rcases Nat.lt_or_ge 72902258659717 n with h10 | h10
          · -- n > 72902258659717
            rcases Nat.lt_or_ge 73082672515373 n with h12 | h12
            · -- n > 73082672515373
              exact RamareSaouter2003.prime_interval_nat_ladder_c03637 n (by omega) (by omega)
            · -- n <= 73082672515373
              exact RamareSaouter2003.prime_interval_nat_ladder_c03636 n (by omega) (by omega)
          · -- n <= 72902258659717
            exact RamareSaouter2003.prime_interval_nat_ladder_c03635 n (by omega) (by omega)
        · -- n <= 72722290178467
          rcases Nat.lt_or_ge 72363684944783 n with h10 | h10
          · -- n > 72363684944783
            rcases Nat.lt_or_ge 72542765972641 n with h12 | h12
            · -- n > 72542765972641
              exact RamareSaouter2003.prime_interval_nat_ladder_c03634 n (by omega) (by omega)
            · -- n <= 72542765972641
              exact RamareSaouter2003.prime_interval_nat_ladder_c03633 n (by omega) (by omega)
          · -- n <= 72363684944783
            exact RamareSaouter2003.prime_interval_nat_ladder_c03632 n (by omega) (by omega)
      · -- n <= 72185046001121
        rcases Nat.lt_or_ge 71651770775791 n with h8 | h8
        · -- n > 71651770775791
          rcases Nat.lt_or_ge 71829090003919 n with h10 | h10
          · -- n > 71829090003919
            rcases Nat.lt_or_ge 72006848050387 n with h12 | h12
            · -- n > 72006848050387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03631 n (by omega) (by omega)
            · -- n <= 72006848050387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03630 n (by omega) (by omega)
          · -- n <= 71829090003919
            exact RamareSaouter2003.prime_interval_nat_ladder_c03629 n (by omega) (by omega)
        · -- n <= 71651770775791
          rcases Nat.lt_or_ge 71298444444163 n with h10 | h10
          · -- n > 71298444444163
            rcases Nat.lt_or_ge 71474889282707 n with h12 | h12
            · -- n > 71474889282707
              exact RamareSaouter2003.prime_interval_nat_ladder_c03628 n (by omega) (by omega)
            · -- n <= 71474889282707
              exact RamareSaouter2003.prime_interval_nat_ladder_c03627 n (by omega) (by omega)
          · -- n <= 71298444444163
            exact RamareSaouter2003.prime_interval_nat_ladder_c03626 n (by omega) (by omega)
  · -- n <= 71122435181953
    rcases Nat.lt_or_ge 68873466587267 n with h4 | h4
    · -- n > 68873466587267
      rcases Nat.lt_or_ge 69902476498787 n with h6 | h6
      · -- n > 69902476498787
        rcases Nat.lt_or_ge 70422732432307 n with h8 | h8
        · -- n > 70422732432307
          rcases Nat.lt_or_ge 70771719088589 n with h10 | h10
          · -- n > 70771719088589
            rcases Nat.lt_or_ge 70946860421029 n with h12 | h12
            · -- n > 70946860421029
              exact RamareSaouter2003.prime_interval_nat_ladder_c03625 n (by omega) (by omega)
            · -- n <= 70946860421029
              exact RamareSaouter2003.prime_interval_nat_ladder_c03624 n (by omega) (by omega)
          · -- n <= 70771719088589
            rcases Nat.lt_or_ge 70597010114801 n with h12 | h12
            · -- n > 70597010114801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03623 n (by omega) (by omega)
            · -- n <= 70597010114801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03622 n (by omega) (by omega)
        · -- n <= 70422732432307
          rcases Nat.lt_or_ge 70075466684953 n with h10 | h10
          · -- n > 70075466684953
            rcases Nat.lt_or_ge 70248884976373 n with h12 | h12
            · -- n > 70248884976373
              exact RamareSaouter2003.prime_interval_nat_ladder_c03621 n (by omega) (by omega)
            · -- n <= 70248884976373
              exact RamareSaouter2003.prime_interval_nat_ladder_c03620 n (by omega) (by omega)
          · -- n <= 70075466684953
            exact RamareSaouter2003.prime_interval_nat_ladder_c03619 n (by omega) (by omega)
      · -- n <= 69902476498787
        rcases Nat.lt_or_ge 69386064015017 n with h8 | h8
        · -- n > 69386064015017
          rcases Nat.lt_or_ge 69557776216571 n with h10 | h10
          · -- n > 69557776216571
            rcases Nat.lt_or_ge 69729913360673 n with h12 | h12
            · -- n > 69729913360673
              exact RamareSaouter2003.prime_interval_nat_ladder_c03618 n (by omega) (by omega)
            · -- n <= 69729913360673
              exact RamareSaouter2003.prime_interval_nat_ladder_c03617 n (by omega) (by omega)
          · -- n <= 69557776216571
            exact RamareSaouter2003.prime_interval_nat_ladder_c03616 n (by omega) (by omega)
        · -- n <= 69386064015017
          rcases Nat.lt_or_ge 69043910245601 n with h10 | h10
          · -- n > 69043910245601
            rcases Nat.lt_or_ge 69214775706997 n with h12 | h12
            · -- n > 69214775706997
              exact RamareSaouter2003.prime_interval_nat_ladder_c03615 n (by omega) (by omega)
            · -- n <= 69214775706997
              exact RamareSaouter2003.prime_interval_nat_ladder_c03614 n (by omega) (by omega)
          · -- n <= 69043910245601
            exact RamareSaouter2003.prime_interval_nat_ladder_c03613 n (by omega) (by omega)
    · -- n <= 68873466587267
      rcases Nat.lt_or_ge 67859604371089 n with h6 | h6
      · -- n > 67859604371089
        rcases Nat.lt_or_ge 68364656031491 n with h8 | h8
        · -- n > 68364656031491
          rcases Nat.lt_or_ge 68533840517911 n with h10 | h10
          · -- n > 68533840517911
            rcases Nat.lt_or_ge 68703443691217 n with h12 | h12
            · -- n > 68703443691217
              exact RamareSaouter2003.prime_interval_nat_ladder_c03612 n (by omega) (by omega)
            · -- n <= 68703443691217
              exact RamareSaouter2003.prime_interval_nat_ladder_c03611 n (by omega) (by omega)
          · -- n <= 68533840517911
            exact RamareSaouter2003.prime_interval_nat_ladder_c03610 n (by omega) (by omega)
        · -- n <= 68364656031491
          rcases Nat.lt_or_ge 68027538987829 n with h10 | h10
          · -- n > 68027538987829
            rcases Nat.lt_or_ge 68195889198457 n with h12 | h12
            · -- n > 68195889198457
              exact RamareSaouter2003.prime_interval_nat_ladder_c03609 n (by omega) (by omega)
            · -- n <= 68195889198457
              exact RamareSaouter2003.prime_interval_nat_ladder_c03608 n (by omega) (by omega)
          · -- n <= 68027538987829
            exact RamareSaouter2003.prime_interval_nat_ladder_c03607 n (by omega) (by omega)
      · -- n <= 67859604371089
        rcases Nat.lt_or_ge 67358283837239 n with h8 | h8
        · -- n > 67358283837239
          rcases Nat.lt_or_ge 67524977817953 n with h10 | h10
          · -- n > 67524977817953
            rcases Nat.lt_or_ge 67692084322361 n with h12 | h12
            · -- n > 67692084322361
              exact RamareSaouter2003.prime_interval_nat_ladder_c03606 n (by omega) (by omega)
            · -- n <= 67692084322361
              exact RamareSaouter2003.prime_interval_nat_ladder_c03605 n (by omega) (by omega)
          · -- n <= 67524977817953
            exact RamareSaouter2003.prime_interval_nat_ladder_c03604 n (by omega) (by omega)
        · -- n <= 67358283837239
          rcases Nat.lt_or_ge 67026129375871 n with h10 | h10
          · -- n > 67026129375871
            rcases Nat.lt_or_ge 67192001361827 n with h12 | h12
            · -- n > 67192001361827
              exact RamareSaouter2003.prime_interval_nat_ladder_c03603 n (by omega) (by omega)
            · -- n <= 67192001361827
              exact RamareSaouter2003.prime_interval_nat_ladder_c03602 n (by omega) (by omega)
          · -- n <= 67026129375871
            exact RamareSaouter2003.prime_interval_nat_ladder_c03601 n (by omega) (by omega)
