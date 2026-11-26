-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaR_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:01.730128+00:00
-- url     : https://prove2.me/submissions/31e82867-cf58-46d0-adad-0196907546db

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p : ℝ) (r : ℕ) :
    gammaR p (r + 1) = gammaR p r * (1 - p⁻¹ ^ (r + 1)) := by
  simp [gammaR, Finset.prod_range_succ]
end SharpIntermediateSubgroupBounds
