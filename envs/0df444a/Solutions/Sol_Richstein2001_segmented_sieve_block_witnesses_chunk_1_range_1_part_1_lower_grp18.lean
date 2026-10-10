-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T07:51:03.473215+00:00
-- url     : https://prove2.me/submissions/74688266-a3b3-4309-a0ad-48612798b71d

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0851
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0852
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0853
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0854
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0855
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0856
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0857
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0858
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0859
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0860
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0861
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0862
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0863
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0864
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0865
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0866
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0867
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0868
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0869
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0870
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0871
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0872
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0873
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0874
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0875
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0876
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0877
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0878
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0879
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0880
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0881
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0882
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0883
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0884
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0885
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0886
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0887
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0888
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0889
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0890
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0891
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0892
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0893
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0894
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0895
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0896
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0897
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0898
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0899
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0900

/-! Link reduction: `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp18` (blocks [50008500, 50009000)) from the 50 chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0851` .. `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0900`, which tile that range end to end; a balanced case split on b selects the chunk. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50008500 <= b) (hhi : b < 50009000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50008750 with hc25 | hc25
  · rcases Nat.lt_or_ge b 50008620 with hc12 | hc12
    · rcases Nat.lt_or_ge b 50008560 with hc6 | hc6
      · rcases Nat.lt_or_ge b 50008530 with hc3 | hc3
        · rcases Nat.lt_or_ge b 50008510 with hc1 | hc1
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0851 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008520 with hc2 | hc2
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0852 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0853 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008540 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0854 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008550 with hc5 | hc5
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0855 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0856 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50008590 with hc9 | hc9
        · rcases Nat.lt_or_ge b 50008570 with hc7 | hc7
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0857 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008580 with hc8 | hc8
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0858 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0859 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008600 with hc10 | hc10
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0860 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008610 with hc11 | hc11
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0861 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0862 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50008680 with hc18 | hc18
      · rcases Nat.lt_or_ge b 50008650 with hc15 | hc15
        · rcases Nat.lt_or_ge b 50008630 with hc13 | hc13
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0863 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008640 with hc14 | hc14
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0864 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0865 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008660 with hc16 | hc16
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0866 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008670 with hc17 | hc17
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0867 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0868 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50008710 with hc21 | hc21
        · rcases Nat.lt_or_ge b 50008690 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0869 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008700 with hc20 | hc20
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0870 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0871 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008730 with hc23 | hc23
          · rcases Nat.lt_or_ge b 50008720 with hc22 | hc22
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0872 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0873 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008740 with hc24 | hc24
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0874 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0875 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50008870 with hc37 | hc37
    · rcases Nat.lt_or_ge b 50008810 with hc31 | hc31
      · rcases Nat.lt_or_ge b 50008780 with hc28 | hc28
        · rcases Nat.lt_or_ge b 50008760 with hc26 | hc26
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0876 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008770 with hc27 | hc27
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0877 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0878 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008790 with hc29 | hc29
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0879 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008800 with hc30 | hc30
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0880 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0881 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50008840 with hc34 | hc34
        · rcases Nat.lt_or_ge b 50008820 with hc32 | hc32
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0882 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008830 with hc33 | hc33
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0883 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0884 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008850 with hc35 | hc35
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0885 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008860 with hc36 | hc36
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0886 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0887 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50008930 with hc43 | hc43
      · rcases Nat.lt_or_ge b 50008900 with hc40 | hc40
        · rcases Nat.lt_or_ge b 50008880 with hc38 | hc38
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0888 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008890 with hc39 | hc39
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0889 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0890 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008910 with hc41 | hc41
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0891 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008920 with hc42 | hc42
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0892 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0893 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50008960 with hc46 | hc46
        · rcases Nat.lt_or_ge b 50008940 with hc44 | hc44
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0894 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008950 with hc45 | hc45
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0895 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0896 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50008980 with hc48 | hc48
          · rcases Nat.lt_or_ge b 50008970 with hc47 | hc47
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0897 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0898 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50008990 with hc49 | hc49
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0899 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0900 b hb (by omega) (by omega)
