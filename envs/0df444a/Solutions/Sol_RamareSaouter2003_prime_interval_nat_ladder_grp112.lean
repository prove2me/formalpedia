-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T17:44:22.391255+00:00
-- url     : https://prove2.me/submissions/18e9a894-cd73-4b28-adec-f121500a6875

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05600

theorem solution (n : Nat)
    (hn : 14733209110173557 < n) (hupper : n <= 16970173954204477) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 15812172902451193 n with h2 | h2
  · -- n > 15812172902451193
    rcases Nat.lt_or_ge 16357803889037557 n with h4 | h4
    · -- n > 16357803889037557
      rcases Nat.lt_or_ge 16637646782494753 n with h6 | h6
      · -- n > 16637646782494753
        rcases Nat.lt_or_ge 16779350503771783 n with h8 | h8
        · -- n > 16779350503771783
          rcases Nat.lt_or_ge 16874494337569721 n with h10 | h10
          · -- n > 16874494337569721
            rcases Nat.lt_or_ge 16922264168740919 n with h12 | h12
            · -- n > 16922264168740919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05600 n (by omega) (by omega)
            · -- n <= 16922264168740919
              exact RamareSaouter2003.prime_interval_nat_ladder_c05599 n (by omega) (by omega)
          · -- n <= 16874494337569721
            rcases Nat.lt_or_ge 16826855330750149 n with h12 | h12
            · -- n > 16826855330750149
              exact RamareSaouter2003.prime_interval_nat_ladder_c05598 n (by omega) (by omega)
            · -- n <= 16826855330750149
              exact RamareSaouter2003.prime_interval_nat_ladder_c05597 n (by omega) (by omega)
        · -- n <= 16779350503771783
          rcases Nat.lt_or_ge 16684748706519343 n with h10 | h10
          · -- n > 16684748706519343
            rcases Nat.lt_or_ge 16731978792089023 n with h12 | h12
            · -- n > 16731978792089023
              exact RamareSaouter2003.prime_interval_nat_ladder_c05596 n (by omega) (by omega)
            · -- n <= 16731978792089023
              exact RamareSaouter2003.prime_interval_nat_ladder_c05595 n (by omega) (by omega)
          · -- n <= 16684748706519343
            exact RamareSaouter2003.prime_interval_nat_ladder_c05594 n (by omega) (by omega)
      · -- n <= 16637646782494753
        rcases Nat.lt_or_ge 16497133750462829 n with h8 | h8
        · -- n > 16497133750462829
          rcases Nat.lt_or_ge 16543837645432567 n with h10 | h10
          · -- n > 16543837645432567
            rcases Nat.lt_or_ge 16590676605916667 n with h12 | h12
            · -- n > 16590676605916667
              exact RamareSaouter2003.prime_interval_nat_ladder_c05593 n (by omega) (by omega)
            · -- n <= 16590676605916667
              exact RamareSaouter2003.prime_interval_nat_ladder_c05592 n (by omega) (by omega)
          · -- n <= 16543837645432567
            exact RamareSaouter2003.prime_interval_nat_ladder_c05591 n (by omega) (by omega)
        · -- n <= 16497133750462829
          rcases Nat.lt_or_ge 16404116888993497 n with h10 | h10
          · -- n > 16404116888993497
            rcases Nat.lt_or_ge 16450561797995539 n with h12 | h12
            · -- n > 16450561797995539
              exact RamareSaouter2003.prime_interval_nat_ladder_c05590 n (by omega) (by omega)
            · -- n <= 16450561797995539
              exact RamareSaouter2003.prime_interval_nat_ladder_c05589 n (by omega) (by omega)
          · -- n <= 16404116888993497
            exact RamareSaouter2003.prime_interval_nat_ladder_c05588 n (by omega) (by omega)
    · -- n <= 16357803889037557
      rcases Nat.lt_or_ge 16082681006433047 n with h6 | h6
      · -- n > 16082681006433047
        rcases Nat.lt_or_ge 16219666013840131 n with h8 | h8
        · -- n > 16219666013840131
          rcases Nat.lt_or_ge 16265579370939007 n with h10 | h10
          · -- n > 16265579370939007
            rcases Nat.lt_or_ge 16311623793237701 n with h12 | h12
            · -- n > 16311623793237701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05587 n (by omega) (by omega)
            · -- n <= 16311623793237701
              exact RamareSaouter2003.prime_interval_nat_ladder_c05586 n (by omega) (by omega)
          · -- n <= 16265579370939007
            exact RamareSaouter2003.prime_interval_nat_ladder_c05585 n (by omega) (by omega)
        · -- n <= 16219666013840131
          rcases Nat.lt_or_ge 16128211753489067 n with h10 | h10
          · -- n > 16128211753489067
            rcases Nat.lt_or_ge 16173875026537517 n with h12 | h12
            · -- n > 16173875026537517
              exact RamareSaouter2003.prime_interval_nat_ladder_c05584 n (by omega) (by omega)
            · -- n <= 16173875026537517
              exact RamareSaouter2003.prime_interval_nat_ladder_c05583 n (by omega) (by omega)
          · -- n <= 16128211753489067
            exact RamareSaouter2003.prime_interval_nat_ladder_c05582 n (by omega) (by omega)
      · -- n <= 16082681006433047
        rcases Nat.lt_or_ge 15946852243231837 n with h8 | h8
        · -- n > 15946852243231837
          rcases Nat.lt_or_ge 15992002264085999 n with h10 | h10
          · -- n > 15992002264085999
            rcases Nat.lt_or_ge 16037277170371447 n with h12 | h12
            · -- n > 16037277170371447
              exact RamareSaouter2003.prime_interval_nat_ladder_c05581 n (by omega) (by omega)
            · -- n <= 16037277170371447
              exact RamareSaouter2003.prime_interval_nat_ladder_c05580 n (by omega) (by omega)
          · -- n <= 15992002264085999
            exact RamareSaouter2003.prime_interval_nat_ladder_c05579 n (by omega) (by omega)
        · -- n <= 15946852243231837
          rcases Nat.lt_or_ge 15856940855284043 n with h10 | h10
          · -- n > 15856940855284043
            rcases Nat.lt_or_ge 15901831356519949 n with h12 | h12
            · -- n > 15901831356519949
              exact RamareSaouter2003.prime_interval_nat_ladder_c05578 n (by omega) (by omega)
            · -- n <= 15901831356519949
              exact RamareSaouter2003.prime_interval_nat_ladder_c05577 n (by omega) (by omega)
          · -- n <= 15856940855284043
            exact RamareSaouter2003.prime_interval_nat_ladder_c05576 n (by omega) (by omega)
  · -- n <= 15812172902451193
    rcases Nat.lt_or_ge 15241595804357653 n with h4 | h4
    · -- n > 15241595804357653
      rcases Nat.lt_or_ge 15502343146183763 n with h6 | h6
      · -- n > 15502343146183763
        rcases Nat.lt_or_ge 15634372618972649 n with h8 | h8
        · -- n > 15634372618972649
          rcases Nat.lt_or_ge 15723024716193947 n with h10 | h10
          · -- n > 15723024716193947
            rcases Nat.lt_or_ge 15767534785123879 n with h12 | h12
            · -- n > 15767534785123879
              exact RamareSaouter2003.prime_interval_nat_ladder_c05575 n (by omega) (by omega)
            · -- n <= 15767534785123879
              exact RamareSaouter2003.prime_interval_nat_ladder_c05574 n (by omega) (by omega)
          · -- n <= 15723024716193947
            rcases Nat.lt_or_ge 15678638166390421 n with h12 | h12
            · -- n > 15678638166390421
              exact RamareSaouter2003.prime_interval_nat_ladder_c05573 n (by omega) (by omega)
            · -- n <= 15678638166390421
              exact RamareSaouter2003.prime_interval_nat_ladder_c05572 n (by omega) (by omega)
        · -- n <= 15634372618972649
          rcases Nat.lt_or_ge 15546231001854467 n with h10 | h10
          · -- n > 15546231001854467
            rcases Nat.lt_or_ge 15590239571720563 n with h12 | h12
            · -- n > 15590239571720563
              exact RamareSaouter2003.prime_interval_nat_ladder_c05571 n (by omega) (by omega)
            · -- n <= 15590239571720563
              exact RamareSaouter2003.prime_interval_nat_ladder_c05570 n (by omega) (by omega)
          · -- n <= 15546231001854467
            exact RamareSaouter2003.prime_interval_nat_ladder_c05569 n (by omega) (by omega)
      · -- n <= 15502343146183763
        rcases Nat.lt_or_ge 15371413827532723 n with h8 | h8
        · -- n > 15371413827532723
          rcases Nat.lt_or_ge 15414934823078383 n with h10 | h10
          · -- n > 15414934823078383
            rcases Nat.lt_or_ge 15458578008943549 n with h12 | h12
            · -- n > 15458578008943549
              exact RamareSaouter2003.prime_interval_nat_ladder_c05568 n (by omega) (by omega)
            · -- n <= 15458578008943549
              exact RamareSaouter2003.prime_interval_nat_ladder_c05567 n (by omega) (by omega)
          · -- n <= 15414934823078383
            exact RamareSaouter2003.prime_interval_nat_ladder_c05566 n (by omega) (by omega)
        · -- n <= 15371413827532723
          rcases Nat.lt_or_ge 15284749039367701 n with h10 | h10
          · -- n > 15284749039367701
            rcases Nat.lt_or_ge 15328019477011391 n with h12 | h12
            · -- n > 15328019477011391
              exact RamareSaouter2003.prime_interval_nat_ladder_c05565 n (by omega) (by omega)
            · -- n <= 15328019477011391
              exact RamareSaouter2003.prime_interval_nat_ladder_c05564 n (by omega) (by omega)
          · -- n <= 15284749039367701
            exact RamareSaouter2003.prime_interval_nat_ladder_c05563 n (by omega) (by omega)
    · -- n <= 15241595804357653
      rcases Nat.lt_or_ge 14985241305956879 n with h6 | h6
      · -- n > 14985241305956879
        rcases Nat.lt_or_ge 15112875831131017 n with h8 | h8
        · -- n > 15112875831131017
          rcases Nat.lt_or_ge 15155663653882537 n with h10 | h10
          · -- n > 15155663653882537
            rcases Nat.lt_or_ge 15198566196215621 n with h12 | h12
            · -- n > 15198566196215621
              exact RamareSaouter2003.prime_interval_nat_ladder_c05562 n (by omega) (by omega)
            · -- n <= 15198566196215621
              exact RamareSaouter2003.prime_interval_nat_ladder_c05561 n (by omega) (by omega)
          · -- n <= 15155663653882537
            exact RamareSaouter2003.prime_interval_nat_ladder_c05560 n (by omega) (by omega)
        · -- n <= 15112875831131017
          rcases Nat.lt_or_ge 15027665779560911 n with h10 | h10
          · -- n > 15027665779560911
            rcases Nat.lt_or_ge 15070212083731397 n with h12 | h12
            · -- n > 15070212083731397
              exact RamareSaouter2003.prime_interval_nat_ladder_c05559 n (by omega) (by omega)
            · -- n <= 15070212083731397
              exact RamareSaouter2003.prime_interval_nat_ladder_c05558 n (by omega) (by omega)
          · -- n <= 15027665779560911
            exact RamareSaouter2003.prime_interval_nat_ladder_c05557 n (by omega) (by omega)
      · -- n <= 14985241305956879
        rcases Nat.lt_or_ge 14858685340660267 n with h8 | h8
        · -- n > 14858685340660267
          rcases Nat.lt_or_ge 14900750246077781 n with h10 | h10
          · -- n > 14900750246077781
            rcases Nat.lt_or_ge 14942938171941673 n with h12 | h12
            · -- n > 14942938171941673
              exact RamareSaouter2003.prime_interval_nat_ladder_c05556 n (by omega) (by omega)
            · -- n <= 14942938171941673
              exact RamareSaouter2003.prime_interval_nat_ladder_c05555 n (by omega) (by omega)
          · -- n <= 14900750246077781
            exact RamareSaouter2003.prime_interval_nat_ladder_c05554 n (by omega) (by omega)
        · -- n <= 14858685340660267
          rcases Nat.lt_or_ge 14774920622543051 n with h10 | h10
          · -- n > 14774920622543051
            rcases Nat.lt_or_ge 14816736861943901 n with h12 | h12
            · -- n > 14816736861943901
              exact RamareSaouter2003.prime_interval_nat_ladder_c05553 n (by omega) (by omega)
            · -- n <= 14816736861943901
              exact RamareSaouter2003.prime_interval_nat_ladder_c05552 n (by omega) (by omega)
          · -- n <= 14774920622543051
            exact RamareSaouter2003.prime_interval_nat_ladder_c05551 n (by omega) (by omega)
