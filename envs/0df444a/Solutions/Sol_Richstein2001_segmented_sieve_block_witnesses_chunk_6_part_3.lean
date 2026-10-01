-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:24:09.763692+00:00
-- url     : https://prove2.me/submissions/6d84055e-1382-4790-9c4c-3296b84aa150
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 320000000 ≤ b) (hhi : b < 330000000) :
    ∀ (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n →
      ∃ (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p ∧
        ∃ (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q ∧
          n = p + q := by
  classical
  intro n hn
  by_cases h1 : b < 322000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_1 b hb hlo h1 n hn
  · by_cases h2 : b < 324000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 326000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 328000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_5 b hb (by omega) hhi n hn
