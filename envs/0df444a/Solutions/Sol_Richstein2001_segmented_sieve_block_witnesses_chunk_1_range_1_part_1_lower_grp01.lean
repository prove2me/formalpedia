-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:35:01.681507+00:00
-- url     : https://prove2.me/submissions/793f334b-1fe0-4502-ba51-fa59f3044911

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0001
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0002
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0003
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0004
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0005
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0006
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0007
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0008
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0009
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0010
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0011
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0012
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0013
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0014
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0015
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0016
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0017
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0018
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0019
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0020
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0021
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0022
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0023
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0024
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0025
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0026
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0027
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0028
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0029
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0030
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0031
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0032
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0033
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0034
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0035
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0036
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0037
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0038
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0039
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0040
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0041
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0042
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0043
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0044
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0045
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0046
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0047
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0048
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0049
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0050

/-! Link reduction: `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp01` (blocks [50000000, 50000500)) from the 50 chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0001` .. `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0050`, which tile that range end to end; a balanced case split on b selects the chunk. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50000000 <= b) (hhi : b < 50000500) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50000250 with hc25 | hc25
  · rcases Nat.lt_or_ge b 50000120 with hc12 | hc12
    · rcases Nat.lt_or_ge b 50000060 with hc6 | hc6
      · rcases Nat.lt_or_ge b 50000030 with hc3 | hc3
        · rcases Nat.lt_or_ge b 50000010 with hc1 | hc1
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0001 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000020 with hc2 | hc2
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0002 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0003 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000040 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0004 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000050 with hc5 | hc5
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0005 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0006 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50000090 with hc9 | hc9
        · rcases Nat.lt_or_ge b 50000070 with hc7 | hc7
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0007 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000080 with hc8 | hc8
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0008 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0009 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000100 with hc10 | hc10
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0010 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000110 with hc11 | hc11
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0011 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0012 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50000180 with hc18 | hc18
      · rcases Nat.lt_or_ge b 50000150 with hc15 | hc15
        · rcases Nat.lt_or_ge b 50000130 with hc13 | hc13
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0013 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000140 with hc14 | hc14
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0014 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0015 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000160 with hc16 | hc16
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0016 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000170 with hc17 | hc17
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0017 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0018 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50000210 with hc21 | hc21
        · rcases Nat.lt_or_ge b 50000190 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0019 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000200 with hc20 | hc20
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0020 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0021 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000230 with hc23 | hc23
          · rcases Nat.lt_or_ge b 50000220 with hc22 | hc22
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0022 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0023 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000240 with hc24 | hc24
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0024 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0025 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50000370 with hc37 | hc37
    · rcases Nat.lt_or_ge b 50000310 with hc31 | hc31
      · rcases Nat.lt_or_ge b 50000280 with hc28 | hc28
        · rcases Nat.lt_or_ge b 50000260 with hc26 | hc26
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0026 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000270 with hc27 | hc27
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0027 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0028 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000290 with hc29 | hc29
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0029 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000300 with hc30 | hc30
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0030 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0031 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50000340 with hc34 | hc34
        · rcases Nat.lt_or_ge b 50000320 with hc32 | hc32
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0032 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000330 with hc33 | hc33
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0033 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0034 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000350 with hc35 | hc35
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0035 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000360 with hc36 | hc36
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0036 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0037 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50000430 with hc43 | hc43
      · rcases Nat.lt_or_ge b 50000400 with hc40 | hc40
        · rcases Nat.lt_or_ge b 50000380 with hc38 | hc38
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0038 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000390 with hc39 | hc39
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0039 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0040 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000410 with hc41 | hc41
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0041 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000420 with hc42 | hc42
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0042 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0043 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50000460 with hc46 | hc46
        · rcases Nat.lt_or_ge b 50000440 with hc44 | hc44
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0044 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000450 with hc45 | hc45
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0045 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0046 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50000480 with hc48 | hc48
          · rcases Nat.lt_or_ge b 50000470 with hc47 | hc47
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0047 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0048 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50000490 with hc49 | hc49
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0049 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0050 b hb (by omega) (by omega)
