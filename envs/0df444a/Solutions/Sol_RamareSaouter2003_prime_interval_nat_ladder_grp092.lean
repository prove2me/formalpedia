-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T11:36:09.481897+00:00
-- url     : https://prove2.me/submissions/27ad6a58-ce01-4233-8d7c-01cb830a47a5

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04600

theorem solution (n : Nat)
    (hn : 872308179808937 < n) (hupper : n <= 1004703773149963) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 936168310532621 n with h2 | h2
  · -- n > 936168310532621
    rcases Nat.lt_or_ge 968461408968881 n with h4 | h4
    · -- n > 968461408968881
      rcases Nat.lt_or_ge 985027424899279 n with h6 | h6
      · -- n > 985027424899279
        rcases Nat.lt_or_ge 993412472896771 n with h8 | h8
        · -- n > 993412472896771
          rcases Nat.lt_or_ge 999040537990787 n with h10 | h10
          · -- n > 999040537990787
            rcases Nat.lt_or_ge 1001867305296461 n with h12 | h12
            · -- n > 1001867305296461
              exact RamareSaouter2003.prime_interval_nat_ladder_c04600 n (by omega) (by omega)
            · -- n <= 1001867305296461
              exact RamareSaouter2003.prime_interval_nat_ladder_c04599 n (by omega) (by omega)
          · -- n <= 999040537990787
            rcases Nat.lt_or_ge 996222118698361 n with h12 | h12
            · -- n > 996222118698361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04598 n (by omega) (by omega)
            · -- n <= 996222118698361
              exact RamareSaouter2003.prime_interval_nat_ladder_c04597 n (by omega) (by omega)
        · -- n <= 993412472896771
          rcases Nat.lt_or_ge 987813630566251 n with h10 | h10
          · -- n > 987813630566251
            rcases Nat.lt_or_ge 990608052157769 n with h12 | h12
            · -- n > 990608052157769
              exact RamareSaouter2003.prime_interval_nat_ladder_c04596 n (by omega) (by omega)
            · -- n <= 990608052157769
              exact RamareSaouter2003.prime_interval_nat_ladder_c04595 n (by omega) (by omega)
          · -- n <= 987813630566251
            exact RamareSaouter2003.prime_interval_nat_ladder_c04594 n (by omega) (by omega)
      · -- n <= 985027424899279
        rcases Nat.lt_or_ge 976709166523591 n with h8 | h8
        · -- n > 976709166523591
          rcases Nat.lt_or_ge 979474328755301 n with h10 | h10
          · -- n > 979474328755301
            rcases Nat.lt_or_ge 982246782919079 n with h12 | h12
            · -- n > 982246782919079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04593 n (by omega) (by omega)
            · -- n <= 982246782919079
              exact RamareSaouter2003.prime_interval_nat_ladder_c04592 n (by omega) (by omega)
          · -- n <= 979474328755301
            exact RamareSaouter2003.prime_interval_nat_ladder_c04591 n (by omega) (by omega)
        · -- n <= 976709166523591
          rcases Nat.lt_or_ge 971203036257451 n with h10 | h10
          · -- n > 971203036257451
            rcases Nat.lt_or_ge 973952221184893 n with h12 | h12
            · -- n > 973952221184893
              exact RamareSaouter2003.prime_interval_nat_ladder_c04590 n (by omega) (by omega)
            · -- n <= 973952221184893
              exact RamareSaouter2003.prime_interval_nat_ladder_c04589 n (by omega) (by omega)
          · -- n <= 971203036257451
            exact RamareSaouter2003.prime_interval_nat_ladder_c04588 n (by omega) (by omega)
    · -- n <= 968461408968881
      rcases Nat.lt_or_ge 952176643298653 n with h6 | h6
      · -- n > 952176643298653
        rcases Nat.lt_or_ge 960283885264597 n with h8 | h8
        · -- n > 960283885264597
          rcases Nat.lt_or_ge 963000950294879 n with h10 | h10
          · -- n > 963000950294879
            rcases Nat.lt_or_ge 965727323177857 n with h12 | h12
            · -- n > 965727323177857
              exact RamareSaouter2003.prime_interval_nat_ladder_c04587 n (by omega) (by omega)
            · -- n <= 965727323177857
              exact RamareSaouter2003.prime_interval_nat_ladder_c04586 n (by omega) (by omega)
          · -- n <= 963000950294879
            exact RamareSaouter2003.prime_interval_nat_ladder_c04585 n (by omega) (by omega)
        · -- n <= 960283885264597
          rcases Nat.lt_or_ge 954871654459447 n with h10 | h10
          · -- n > 954871654459447
            rcases Nat.lt_or_ge 957574371617077 n with h12 | h12
            · -- n > 957574371617077
              exact RamareSaouter2003.prime_interval_nat_ladder_c04584 n (by omega) (by omega)
            · -- n <= 957574371617077
              exact RamareSaouter2003.prime_interval_nat_ladder_c04583 n (by omega) (by omega)
          · -- n <= 954871654459447
            exact RamareSaouter2003.prime_interval_nat_ladder_c04582 n (by omega) (by omega)
      · -- n <= 952176643298653
        rcases Nat.lt_or_ge 944138243752577 n with h8 | h8
        · -- n > 944138243752577
          rcases Nat.lt_or_ge 946810294239871 n with h10 | h10
          · -- n > 946810294239871
            rcases Nat.lt_or_ge 949488582979331 n with h12 | h12
            · -- n > 949488582979331
              exact RamareSaouter2003.prime_interval_nat_ladder_c04581 n (by omega) (by omega)
            · -- n <= 949488582979331
              exact RamareSaouter2003.prime_interval_nat_ladder_c04580 n (by omega) (by omega)
          · -- n <= 946810294239871
            exact RamareSaouter2003.prime_interval_nat_ladder_c04579 n (by omega) (by omega)
        · -- n <= 944138243752577
          rcases Nat.lt_or_ge 938817790534537 n with h10 | h10
          · -- n > 938817790534537
            rcases Nat.lt_or_ge 941473591160929 n with h12 | h12
            · -- n > 941473591160929
              exact RamareSaouter2003.prime_interval_nat_ladder_c04578 n (by omega) (by omega)
            · -- n <= 941473591160929
              exact RamareSaouter2003.prime_interval_nat_ladder_c04577 n (by omega) (by omega)
          · -- n <= 938817790534537
            exact RamareSaouter2003.prime_interval_nat_ladder_c04576 n (by omega) (by omega)
  · -- n <= 936168310532621
    rcases Nat.lt_or_ge 902399661834943 n with h4 | h4
    · -- n > 902399661834943
      rcases Nat.lt_or_ge 917831116216873 n with h6 | h6
      · -- n > 917831116216873
        rcases Nat.lt_or_ge 925645008668363 n with h8 | h8
        · -- n > 925645008668363
          rcases Nat.lt_or_ge 930890406410329 n with h10 | h10
          · -- n > 930890406410329
            rcases Nat.lt_or_ge 933525875073131 n with h12 | h12
            · -- n > 933525875073131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04575 n (by omega) (by omega)
            · -- n <= 933525875073131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04574 n (by omega) (by omega)
          · -- n <= 930890406410329
            rcases Nat.lt_or_ge 928265490715141 n with h12 | h12
            · -- n > 928265490715141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04573 n (by omega) (by omega)
            · -- n <= 928265490715141
              exact RamareSaouter2003.prime_interval_nat_ladder_c04572 n (by omega) (by omega)
        · -- n <= 925645008668363
          rcases Nat.lt_or_ge 920427898975063 n with h10 | h10
          · -- n > 920427898975063
            rcases Nat.lt_or_ge 923031694886911 n with h12 | h12
            · -- n > 923031694886911
              exact RamareSaouter2003.prime_interval_nat_ladder_c04571 n (by omega) (by omega)
            · -- n <= 923031694886911
              exact RamareSaouter2003.prime_interval_nat_ladder_c04570 n (by omega) (by omega)
          · -- n <= 920427898975063
            exact RamareSaouter2003.prime_interval_nat_ladder_c04569 n (by omega) (by omega)
      · -- n <= 917831116216873
        rcases Nat.lt_or_ge 910082442466891 n with h8 | h8
        · -- n > 910082442466891
          rcases Nat.lt_or_ge 912657495738029 n with h10 | h10
          · -- n > 912657495738029
            rcases Nat.lt_or_ge 915240300370657 n with h12 | h12
            · -- n > 915240300370657
              exact RamareSaouter2003.prime_interval_nat_ladder_c04568 n (by omega) (by omega)
            · -- n <= 915240300370657
              exact RamareSaouter2003.prime_interval_nat_ladder_c04567 n (by omega) (by omega)
          · -- n <= 912657495738029
            exact RamareSaouter2003.prime_interval_nat_ladder_c04566 n (by omega) (by omega)
        · -- n <= 910082442466891
          rcases Nat.lt_or_ge 904952276794781 n with h10 | h10
          · -- n > 904952276794781
            rcases Nat.lt_or_ge 907513981643747 n with h12 | h12
            · -- n > 907513981643747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04565 n (by omega) (by omega)
            · -- n <= 907513981643747
              exact RamareSaouter2003.prime_interval_nat_ladder_c04564 n (by omega) (by omega)
          · -- n <= 904952276794781
            exact RamareSaouter2003.prime_interval_nat_ladder_c04563 n (by omega) (by omega)
    · -- n <= 902399661834943
      rcases Nat.lt_or_ge 887227108458991 n with h6 | h6
      · -- n > 887227108458991
        rcases Nat.lt_or_ge 894782349659567 n with h8 | h8
        · -- n > 894782349659567
          rcases Nat.lt_or_ge 897314770786817 n with h10 | h10
          · -- n > 897314770786817
            rcases Nat.lt_or_ge 899852209591789 n with h12 | h12
            · -- n > 899852209591789
              exact RamareSaouter2003.prime_interval_nat_ladder_c04562 n (by omega) (by omega)
            · -- n <= 899852209591789
              exact RamareSaouter2003.prime_interval_nat_ladder_c04561 n (by omega) (by omega)
          · -- n <= 897314770786817
            exact RamareSaouter2003.prime_interval_nat_ladder_c04560 n (by omega) (by omega)
        · -- n <= 894782349659567
          rcases Nat.lt_or_ge 889737547447607 n with h10 | h10
          · -- n > 889737547447607
            rcases Nat.lt_or_ge 892256553108917 n with h12 | h12
            · -- n > 892256553108917
              exact RamareSaouter2003.prime_interval_nat_ladder_c04559 n (by omega) (by omega)
            · -- n <= 892256553108917
              exact RamareSaouter2003.prime_interval_nat_ladder_c04558 n (by omega) (by omega)
          · -- n <= 889737547447607
            exact RamareSaouter2003.prime_interval_nat_ladder_c04557 n (by omega) (by omega)
      · -- n <= 887227108458991
        rcases Nat.lt_or_ge 879735753946513 n with h8 | h8
        · -- n > 879735753946513
          rcases Nat.lt_or_ge 882226135795391 n with h10 | h10
          · -- n > 882226135795391
            rcases Nat.lt_or_ge 884723904370667 n with h12 | h12
            · -- n > 884723904370667
              exact RamareSaouter2003.prime_interval_nat_ladder_c04556 n (by omega) (by omega)
            · -- n <= 884723904370667
              exact RamareSaouter2003.prime_interval_nat_ladder_c04555 n (by omega) (by omega)
          · -- n <= 882226135795391
            exact RamareSaouter2003.prime_interval_nat_ladder_c04554 n (by omega) (by omega)
        · -- n <= 879735753946513
          rcases Nat.lt_or_ge 874777561629077 n with h10 | h10
          · -- n > 874777561629077
            rcases Nat.lt_or_ge 877253633132131 n with h12 | h12
            · -- n > 877253633132131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04553 n (by omega) (by omega)
            · -- n <= 877253633132131
              exact RamareSaouter2003.prime_interval_nat_ladder_c04552 n (by omega) (by omega)
          · -- n <= 874777561629077
            exact RamareSaouter2003.prime_interval_nat_ladder_c04551 n (by omega) (by omega)
