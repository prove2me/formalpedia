-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_inv_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:37.749938+00:00
-- url     : https://prove2.me/submissions/70115aad-9dd6-4d9b-b2f0-0005f5ca7e71

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_partial_tendsto


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun r : ℕ ↦ (gammaR p r)⁻¹) atTop (nhds (eulerC p)) := by
  simpa [gammaR, Finset.prod_inv_distrib] using eulerC_partial_tendsto hp
end SharpIntermediateSubgroupBounds
