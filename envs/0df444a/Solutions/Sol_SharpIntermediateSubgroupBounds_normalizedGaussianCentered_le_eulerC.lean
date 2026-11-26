-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianCentered_le_eulerC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:13.410903+00:00
-- url     : https://prove2.me/submissions/55f0c472-34f9-4338-a7bd-6bddd8a014d1

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_le_eulerC

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} {j : ℤ}
    (hp : 2 ≤ p) :
    normalizedGaussianCentered p a j ≤
      eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs) := by
  exact normalizedGaussianRight_le_eulerC hp
end SharpIntermediateSubgroupBounds
