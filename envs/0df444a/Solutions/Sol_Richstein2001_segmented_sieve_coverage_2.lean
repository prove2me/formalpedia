-- Prove2me | solution 2 for Richstein2001.segmented_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:29:45.82605+00:00
-- url     : https://prove2.me/submissions/df6f6b30-87cf-4962-9460-ee579865a1e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses
import Theorems.Thm_GoldbachSieve_witnesses_cover_finset
import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

theorem solution (b : ℕ) (hb : b < 400000001) :
    ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 5569 (b * 1000000 - 5569)
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 := by
  exact GoldbachSieve.witnesses_cover_finset _ 5569 (b * 1000000 - 5569)
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000
    (Richstein2001.segmented_sieve_block_witnesses b hb)