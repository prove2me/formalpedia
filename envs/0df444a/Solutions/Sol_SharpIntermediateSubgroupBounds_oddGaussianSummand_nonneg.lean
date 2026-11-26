-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.oddGaussianSummand_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:27.438616+00:00
-- url     : https://prove2.me/submissions/936ffcea-e631-4e2d-845f-fcbcd9ffbe62

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_nonneg

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ oddGaussianSummand p a j := by
  have hscale : 0 ≤ quarterShiftScale (p : ℝ) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (by norm_num) hscale)
    (normalizedOddGaussianRight_nonneg hp)
end SharpIntermediateSubgroupBounds
