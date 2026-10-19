-- Prove2me | solution 4 for Richstein2001.segmented_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T10:31:40.381428+00:00
-- url     : https://prove2.me/submissions/b389eb39-3dfb-450d-9c14-6f00cf1028c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses
import Theorems.Thm_GoldbachSieve_mem_pairSums

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

theorem solution (b : ℕ) (hb : b < 400000001) :
    ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 5569 (b * 1000000 - 5569)
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 := by
  intro n hn
  rw [GoldbachSieve.mem_pairSums]
  exact Richstein2001.segmented_sieve_block_witnesses b hb n hn
