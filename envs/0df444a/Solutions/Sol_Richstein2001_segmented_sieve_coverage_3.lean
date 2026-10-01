-- Prove2me | solution 3 for Richstein2001.segmented_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T14:18:39.772992+00:00
-- url     : https://prove2.me/submissions/d572e68d-aeef-49a5-8b0d-b988c2cb9a08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_GoldbachSieve_witnesses_cover_finset
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses

open Richstein2001

theorem solution (b : ℕ) (hb : b < 400000001) :
    ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 5569 (b * 1000000 - 5569)
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 := by
  refine GoldbachSieve.witnesses_cover_finset _ 5569 (b * 1000000 - 5569)
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 ?_
  intro n hn
  exact segmented_sieve_block_witnesses b hb n hn
