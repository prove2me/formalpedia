-- Prove2me | solution 2 for Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:54:32.979874+00:00
-- url     : https://prove2.me/submissions/54408c14-a742-41be-83af-9035205b698b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_5

theorem solution (b : Nat) (hb : b < 400000001) (hlo : 0 <= b)
    (hloRange : 25000000 <= b) (hhi : b < 50000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun (p : Nat) => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists (fun (q : Nat) => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)))) := by
  intro n hn
  by_cases h1 : b < 30000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_1
      b hb hlo hloRange h1 n hn
  · by_cases h2 : b < 35000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_2
        b hb hlo (by omega) h2 n hn
    · by_cases h3 : b < 40000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_3
          b hb hlo (by omega) h3 n hn
      · by_cases h4 : b < 45000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_4
            b hb hlo (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_5
            b hb hlo (by omega) hhi n hn