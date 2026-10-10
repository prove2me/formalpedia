-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T06:02:54.488694+00:00
-- url     : https://prove2.me/submissions/406f0379-fbdf-4fc6-87ad-b4bd05c2438e

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0701
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0702
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0703
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0704
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0705
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0706
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0707
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0708
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0709
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0710
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0711
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0712
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0713
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0714
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0715
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0716
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0717
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0718
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0719
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0720
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0721
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0722
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0723
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0724
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0725
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0726
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0727
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0728
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0729
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0730
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0731
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0732
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0733
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0734
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0735
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0736
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0737
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0738
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0739
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0740
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0741
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0742
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0743
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0744
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0745
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0746
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0747
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0748
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0749
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0750

/-! Link reduction: `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp15` (blocks [50007000, 50007500)) from the 50 chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0701` .. `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0750`, which tile that range end to end; a balanced case split on b selects the chunk. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50007000 <= b) (hhi : b < 50007500) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50007250 with hc25 | hc25
  · rcases Nat.lt_or_ge b 50007120 with hc12 | hc12
    · rcases Nat.lt_or_ge b 50007060 with hc6 | hc6
      · rcases Nat.lt_or_ge b 50007030 with hc3 | hc3
        · rcases Nat.lt_or_ge b 50007010 with hc1 | hc1
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0701 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007020 with hc2 | hc2
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0702 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0703 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007040 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0704 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007050 with hc5 | hc5
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0705 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0706 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007090 with hc9 | hc9
        · rcases Nat.lt_or_ge b 50007070 with hc7 | hc7
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0707 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007080 with hc8 | hc8
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0708 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0709 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007100 with hc10 | hc10
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0710 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007110 with hc11 | hc11
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0711 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0712 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50007180 with hc18 | hc18
      · rcases Nat.lt_or_ge b 50007150 with hc15 | hc15
        · rcases Nat.lt_or_ge b 50007130 with hc13 | hc13
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0713 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007140 with hc14 | hc14
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0714 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0715 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007160 with hc16 | hc16
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0716 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007170 with hc17 | hc17
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0717 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0718 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007210 with hc21 | hc21
        · rcases Nat.lt_or_ge b 50007190 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0719 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007200 with hc20 | hc20
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0720 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0721 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007230 with hc23 | hc23
          · rcases Nat.lt_or_ge b 50007220 with hc22 | hc22
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0722 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0723 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007240 with hc24 | hc24
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0724 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0725 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50007370 with hc37 | hc37
    · rcases Nat.lt_or_ge b 50007310 with hc31 | hc31
      · rcases Nat.lt_or_ge b 50007280 with hc28 | hc28
        · rcases Nat.lt_or_ge b 50007260 with hc26 | hc26
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0726 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007270 with hc27 | hc27
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0727 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0728 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007290 with hc29 | hc29
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0729 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007300 with hc30 | hc30
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0730 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0731 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007340 with hc34 | hc34
        · rcases Nat.lt_or_ge b 50007320 with hc32 | hc32
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0732 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007330 with hc33 | hc33
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0733 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0734 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007350 with hc35 | hc35
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0735 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007360 with hc36 | hc36
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0736 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0737 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50007430 with hc43 | hc43
      · rcases Nat.lt_or_ge b 50007400 with hc40 | hc40
        · rcases Nat.lt_or_ge b 50007380 with hc38 | hc38
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0738 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007390 with hc39 | hc39
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0739 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0740 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007410 with hc41 | hc41
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0741 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007420 with hc42 | hc42
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0742 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0743 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50007460 with hc46 | hc46
        · rcases Nat.lt_or_ge b 50007440 with hc44 | hc44
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0744 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007450 with hc45 | hc45
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0745 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0746 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007480 with hc48 | hc48
          · rcases Nat.lt_or_ge b 50007470 with hc47 | hc47
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0747 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0748 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50007490 with hc49 | hc49
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0749 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0750 b hb (by omega) (by omega)
