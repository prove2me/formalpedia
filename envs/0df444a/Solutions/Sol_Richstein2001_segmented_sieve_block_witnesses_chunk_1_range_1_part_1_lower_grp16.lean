-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T06:38:29.809098+00:00
-- url     : https://prove2.me/submissions/ee66e73d-e698-450e-8d8c-e8496bb14f4b

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0751
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0752
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0753
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0754
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0755
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0756
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0757
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0758
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0759
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0760
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0761
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0762
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0763
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0764
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0765
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0766
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0767
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0768
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0769
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0770
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0771
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0772
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0773
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0774
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0775
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0776
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0777
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0778
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0779
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0780
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0781
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0782
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0783
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0784
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0785
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0786
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0787
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0788
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0789
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0790
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0791
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0792
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0793
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0794
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0795
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0796
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0797
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0798
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0799
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0800

/-! Link reduction: `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp16` (blocks [50007500, 50008000)) from the 50 chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0751` .. `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0800`, which tile that range end to end; a balanced case split on b selects the chunk. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50007500 <= b) (hhi : b < 50008000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50007750 with hc25 | hc25
  · rcases Nat.lt_or_ge b 50007620 with hc12 | hc12
    · rcases Nat.lt_or_ge b 50007560 with hc6 | hc6
      · rcases Nat.lt_or_ge b 50007530 with hc3 | hc3
        · rcases Nat.lt_or_ge b 50007510 with hc1 | hc1
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0751 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007520 with hc2 | hc2
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0752 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0753 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007540 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0754 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007550 with hc5 | hc5
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0755 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0756 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007590 with hc9 | hc9
        · rcases Nat.lt_or_ge b 50007570 with hc7 | hc7
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0757 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007580 with hc8 | hc8
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0758 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0759 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007600 with hc10 | hc10
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0760 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007610 with hc11 | hc11
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0761 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0762 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50007680 with hc18 | hc18
      · rcases Nat.lt_or_ge b 50007650 with hc15 | hc15
        · rcases Nat.lt_or_ge b 50007630 with hc13 | hc13
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0763 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007640 with hc14 | hc14
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0764 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0765 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007660 with hc16 | hc16
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0766 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007670 with hc17 | hc17
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0767 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0768 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007710 with hc21 | hc21
        · rcases Nat.lt_or_ge b 50007690 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0769 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007700 with hc20 | hc20
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0770 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0771 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007730 with hc23 | hc23
          · rcases Nat.lt_or_ge b 50007720 with hc22 | hc22
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0772 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0773 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007740 with hc24 | hc24
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0774 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0775 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50007870 with hc37 | hc37
    · rcases Nat.lt_or_ge b 50007810 with hc31 | hc31
      · rcases Nat.lt_or_ge b 50007780 with hc28 | hc28
        · rcases Nat.lt_or_ge b 50007760 with hc26 | hc26
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0776 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007770 with hc27 | hc27
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0777 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0778 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007790 with hc29 | hc29
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0779 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007800 with hc30 | hc30
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0780 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0781 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007840 with hc34 | hc34
        · rcases Nat.lt_or_ge b 50007820 with hc32 | hc32
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0782 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007830 with hc33 | hc33
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0783 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0784 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007850 with hc35 | hc35
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0785 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007860 with hc36 | hc36
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0786 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0787 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50007930 with hc43 | hc43
      · rcases Nat.lt_or_ge b 50007900 with hc40 | hc40
        · rcases Nat.lt_or_ge b 50007880 with hc38 | hc38
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0788 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007890 with hc39 | hc39
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0789 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0790 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007910 with hc41 | hc41
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0791 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007920 with hc42 | hc42
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0792 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0793 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007960 with hc46 | hc46
        · rcases Nat.lt_or_ge b 50007940 with hc44 | hc44
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0794 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007950 with hc45 | hc45
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0795 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0796 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007980 with hc48 | hc48
          · rcases Nat.lt_or_ge b 50007970 with hc47 | hc47
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0797 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0798 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007990 with hc49 | hc49
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0799 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0800 b hb (by omega) (by omega)
