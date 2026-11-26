-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianCentered_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:59.105997+00:00
-- url     : https://prove2.me/submissions/d31e0f01-c3a9-4ee0-9d2e-956a5cfdd1b7

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_tendsto

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} {j : ℤ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ normalizedGaussianCentered p a j) atTop
      (nhds (eulerC (p : ℝ) *
        (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs))) := by
  exact normalizedGaussianRight_tendsto hp
end SharpIntermediateSubgroupBounds
