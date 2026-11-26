-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.evenUSummand_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:21.837458+00:00
-- url     : https://prove2.me/submissions/b436c050-07c3-4b0a-9271-3f3a1acbb5da

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_pos

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ evenUSummand p a j := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  unfold evenUSummand
  by_cases hj0 : j = 0
  · rw [if_pos hj0]
    exact (inv_pos.mpr (gammaR_pos hp1 a)).le
  · rw [if_neg hj0]
    by_cases hja : j ≤ a
    · rw [if_pos hja]
      exact mul_nonneg (by positivity)
        (add_nonneg (inv_pos.mpr (gammaR_pos hp1 (a + j))).le
          (inv_pos.mpr (gammaR_pos hp1 (a - j))).le)
    · rw [if_neg hja]
end SharpIntermediateSubgroupBounds
