-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.evenGaussianSummand_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:51.423089+00:00
-- url     : https://prove2.me/submissions/0e42a522-5aa7-4fb3-8d90-669ef4284aff

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
theorem _root_.solution {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ evenGaussianSummand p a j) atTop
      (nhds (evenGaussianLimitSummand p j)) := by
  exact tendsto_const_nhds.mul (normalizedGaussianRight_tendsto hp)
end SharpIntermediateSubgroupBounds
