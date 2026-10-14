-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T23:28:12.457973+00:00
-- url     : https://prove2.me/submissions/3352f3ee-5b98-4354-aab8-15925f44dd76

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02700

theorem solution (n : Nat)
    (hn : 6388603926769 < n) (hupper : n <= 7228992803521) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 6795820172137 n with h2 | h2
  · -- n > 6795820172137
    rcases Nat.lt_or_ge 7000404205499 n with h4 | h4
    · -- n > 7000404205499
      rcases Nat.lt_or_ge 7104994342489 n with h6 | h6
      · -- n > 7104994342489
        rcases Nat.lt_or_ge 7157873949041 n with h8 | h8
        · -- n > 7157873949041
          rcases Nat.lt_or_ge 7193345485037 n with h10 | h10
          · -- n > 7193345485037
            rcases Nat.lt_or_ge 7211147117113 n with h12 | h12
            · -- n > 7211147117113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02700 n (by omega) (by omega)
            · -- n <= 7211147117113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02699 n (by omega) (by omega)
          · -- n <= 7193345485037
            rcases Nat.lt_or_ge 7175587798513 n with h12 | h12
            · -- n > 7175587798513
              exact RamareSaouter2003.prime_interval_nat_ladder_c02698 n (by omega) (by omega)
            · -- n <= 7175587798513
              exact RamareSaouter2003.prime_interval_nat_ladder_c02697 n (by omega) (by omega)
        · -- n <= 7157873949041
          rcases Nat.lt_or_ge 7122577328833 n with h10 | h10
          · -- n > 7122577328833
            rcases Nat.lt_or_ge 7140203828437 n with h12 | h12
            · -- n > 7140203828437
              exact RamareSaouter2003.prime_interval_nat_ladder_c02696 n (by omega) (by omega)
            · -- n <= 7140203828437
              exact RamareSaouter2003.prime_interval_nat_ladder_c02695 n (by omega) (by omega)
          · -- n <= 7122577328833
            exact RamareSaouter2003.prime_interval_nat_ladder_c02694 n (by omega) (by omega)
      · -- n <= 7104994342489
        rcases Nat.lt_or_ge 7052505389953 n with h8 | h8
        · -- n > 7052505389953
          rcases Nat.lt_or_ge 7069958480027 n with h10 | h10
          · -- n > 7069958480027
            rcases Nat.lt_or_ge 7087454761909 n with h12 | h12
            · -- n > 7087454761909
              exact RamareSaouter2003.prime_interval_nat_ladder_c02693 n (by omega) (by omega)
            · -- n <= 7087454761909
              exact RamareSaouter2003.prime_interval_nat_ladder_c02692 n (by omega) (by omega)
          · -- n <= 7069958480027
            exact RamareSaouter2003.prime_interval_nat_ladder_c02691 n (by omega) (by omega)
        · -- n <= 7052505389953
          rcases Nat.lt_or_ge 7017728358911 n with h10 | h10
          · -- n > 7017728358911
            rcases Nat.lt_or_ge 7035095385013 n with h12 | h12
            · -- n > 7035095385013
              exact RamareSaouter2003.prime_interval_nat_ladder_c02690 n (by omega) (by omega)
            · -- n <= 7035095385013
              exact RamareSaouter2003.prime_interval_nat_ladder_c02689 n (by omega) (by omega)
          · -- n <= 7017728358911
            exact RamareSaouter2003.prime_interval_nat_ladder_c02688 n (by omega) (by omega)
    · -- n <= 7000404205499
      rcases Nat.lt_or_ge 6897353703733 n with h6 | h6
      · -- n > 6897353703733
        rcases Nat.lt_or_ge 6948687924487 n with h8 | h8
        · -- n > 6948687924487
          rcases Nat.lt_or_ge 6965884093711 n with h10 | h10
          · -- n > 6965884093711
            rcases Nat.lt_or_ge 6983122818953 n with h12 | h12
            · -- n > 6983122818953
              exact RamareSaouter2003.prime_interval_nat_ladder_c02687 n (by omega) (by omega)
            · -- n <= 6983122818953
              exact RamareSaouter2003.prime_interval_nat_ladder_c02686 n (by omega) (by omega)
          · -- n <= 6965884093711
            exact RamareSaouter2003.prime_interval_nat_ladder_c02685 n (by omega) (by omega)
        · -- n <= 6948687924487
          rcases Nat.lt_or_ge 6914422834351 n with h10 | h10
          · -- n > 6914422834351
            rcases Nat.lt_or_ge 6931534206481 n with h12 | h12
            · -- n > 6931534206481
              exact RamareSaouter2003.prime_interval_nat_ladder_c02684 n (by omega) (by omega)
            · -- n <= 6931534206481
              exact RamareSaouter2003.prime_interval_nat_ladder_c02683 n (by omega) (by omega)
          · -- n <= 6914422834351
            exact RamareSaouter2003.prime_interval_nat_ladder_c02682 n (by omega) (by omega)
      · -- n <= 6897353703733
        rcases Nat.lt_or_ge 6846398720027 n with h8 | h8
        · -- n > 6846398720027
          rcases Nat.lt_or_ge 6863341750493 n with h10 | h10
          · -- n > 6863341750493
            rcases Nat.lt_or_ge 6880326710443 n with h12 | h12
            · -- n > 6880326710443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02681 n (by omega) (by omega)
            · -- n <= 6880326710443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02680 n (by omega) (by omega)
          · -- n <= 6863341750493
            exact RamareSaouter2003.prime_interval_nat_ladder_c02679 n (by omega) (by omega)
        · -- n <= 6846398720027
          rcases Nat.lt_or_ge 6812638034021 n with h10 | h10
          · -- n > 6812638034021
            rcases Nat.lt_or_ge 6829497515579 n with h12 | h12
            · -- n > 6829497515579
              exact RamareSaouter2003.prime_interval_nat_ladder_c02678 n (by omega) (by omega)
            · -- n <= 6829497515579
              exact RamareSaouter2003.prime_interval_nat_ladder_c02677 n (by omega) (by omega)
          · -- n <= 6812638034021
            exact RamareSaouter2003.prime_interval_nat_ladder_c02676 n (by omega) (by omega)
  · -- n <= 6795820172137
    rcases Nat.lt_or_ge 6580928962859 n with h4 | h4
    · -- n > 6580928962859
      rcases Nat.lt_or_ge 6679251894013 n with h6 | h6
      · -- n > 6679251894013
        rcases Nat.lt_or_ge 6728962871321 n with h8 | h8
        · -- n > 6728962871321
          rcases Nat.lt_or_ge 6762308897009 n with h10 | h10
          · -- n > 6762308897009
            rcases Nat.lt_or_ge 6779043827321 n with h12 | h12
            · -- n > 6779043827321
              exact RamareSaouter2003.prime_interval_nat_ladder_c02675 n (by omega) (by omega)
            · -- n <= 6779043827321
              exact RamareSaouter2003.prime_interval_nat_ladder_c02674 n (by omega) (by omega)
          · -- n <= 6762308897009
            rcases Nat.lt_or_ge 6745615279037 n with h12 | h12
            · -- n > 6745615279037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02673 n (by omega) (by omega)
            · -- n <= 6745615279037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02672 n (by omega) (by omega)
        · -- n <= 6728962871321
          rcases Nat.lt_or_ge 6695781280147 n with h10 | h10
          · -- n > 6695781280147
            rcases Nat.lt_or_ge 6712351572191 n with h12 | h12
            · -- n > 6712351572191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02671 n (by omega) (by omega)
            · -- n <= 6712351572191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02670 n (by omega) (by omega)
          · -- n <= 6695781280147
            exact RamareSaouter2003.prime_interval_nat_ladder_c02669 n (by omega) (by omega)
      · -- n <= 6679251894013
        rcases Nat.lt_or_ge 6629908162139 n with h8 | h8
        · -- n > 6629908162139
          rcases Nat.lt_or_ge 6646315435597 n with h10 | h10
          · -- n > 6646315435597
            rcases Nat.lt_or_ge 6662763312721 n with h12 | h12
            · -- n > 6662763312721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02668 n (by omega) (by omega)
            · -- n <= 6662763312721
              exact RamareSaouter2003.prime_interval_nat_ladder_c02667 n (by omega) (by omega)
          · -- n <= 6646315435597
            exact RamareSaouter2003.prime_interval_nat_ladder_c02666 n (by omega) (by omega)
        · -- n <= 6629908162139
          rcases Nat.lt_or_ge 6597215025641 n with h10 | h10
          · -- n > 6597215025641
            rcases Nat.lt_or_ge 6613541392193 n with h12 | h12
            · -- n > 6613541392193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02665 n (by omega) (by omega)
            · -- n <= 6613541392193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02664 n (by omega) (by omega)
          · -- n <= 6597215025641
            exact RamareSaouter2003.prime_interval_nat_ladder_c02663 n (by omega) (by omega)
    · -- n <= 6580928962859
      rcases Nat.lt_or_ge 6484053409129 n with h6 | h6
      · -- n > 6484053409129
        rcases Nat.lt_or_ge 6532311602867 n with h8 | h8
        · -- n > 6532311602867
          rcases Nat.lt_or_ge 6548477350609 n with h10 | h10
          · -- n > 6548477350609
            rcases Nat.lt_or_ge 6564683104297 n with h12 | h12
            · -- n > 6564683104297
              exact RamareSaouter2003.prime_interval_nat_ladder_c02662 n (by omega) (by omega)
            · -- n <= 6564683104297
              exact RamareSaouter2003.prime_interval_nat_ladder_c02661 n (by omega) (by omega)
          · -- n <= 6548477350609
            exact RamareSaouter2003.prime_interval_nat_ladder_c02660 n (by omega) (by omega)
        · -- n <= 6532311602867
          rcases Nat.lt_or_ge 6500099730529 n with h10 | h10
          · -- n > 6500099730529
            rcases Nat.lt_or_ge 6516185762371 n with h12 | h12
            · -- n > 6516185762371
              exact RamareSaouter2003.prime_interval_nat_ladder_c02659 n (by omega) (by omega)
            · -- n <= 6516185762371
              exact RamareSaouter2003.prime_interval_nat_ladder_c02658 n (by omega) (by omega)
          · -- n <= 6500099730529
            exact RamareSaouter2003.prime_interval_nat_ladder_c02657 n (by omega) (by omega)
      · -- n <= 6484053409129
        rcases Nat.lt_or_ge 6436151728271 n with h8 | h8
        · -- n > 6436151728271
          rcases Nat.lt_or_ge 6452079505691 n with h10 | h10
          · -- n > 6452079505691
            rcases Nat.lt_or_ge 6468046700077 n with h12 | h12
            · -- n > 6468046700077
              exact RamareSaouter2003.prime_interval_nat_ladder_c02656 n (by omega) (by omega)
            · -- n <= 6468046700077
              exact RamareSaouter2003.prime_interval_nat_ladder_c02655 n (by omega) (by omega)
          · -- n <= 6452079505691
            exact RamareSaouter2003.prime_interval_nat_ladder_c02654 n (by omega) (by omega)
        · -- n <= 6436151728271
          rcases Nat.lt_or_ge 6404414035861 n with h10 | h10
          · -- n > 6404414035861
            rcases Nat.lt_or_ge 6420263270633 n with h12 | h12
            · -- n > 6420263270633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02653 n (by omega) (by omega)
            · -- n <= 6420263270633
              exact RamareSaouter2003.prime_interval_nat_ladder_c02652 n (by omega) (by omega)
          · -- n <= 6404414035861
            exact RamareSaouter2003.prime_interval_nat_ladder_c02651 n (by omega) (by omega)
