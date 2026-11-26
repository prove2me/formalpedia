-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:25.525333+00:00
-- url     : https://prove2.me/submissions/55fe16af-0325-4914-91ad-7dc2cdc86cbb

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (gammaR p) atTop (nhds (eulerC p)⁻¹) := by
  have h := (gammaR_inv_tendsto hp).inv₀ (ne_of_gt (eulerC_pos hp))
  simpa using h
end SharpIntermediateSubgroupBounds
