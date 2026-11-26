-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.oddGaussianSummand_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:56.648162+00:00
-- url     : https://prove2.me/submissions/c0a1c4a0-e3cc-4b36-9cce-821241731afa

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_tendsto

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ oddGaussianSummand p a j) atTop
      (nhds (oddGaussianLimitSummand p j)) := by
  exact tendsto_const_nhds.mul (normalizedOddGaussianRight_tendsto hp)
end SharpIntermediateSubgroupBounds
