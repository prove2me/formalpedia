-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qWeight_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:55.446353+00:00
-- url     : https://prove2.me/submissions/f090e915-a34c-4ca4-a2a8-89cdf6ecd0a4

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
theorem _root_.solution (r : ℕ) : qWeight (r + 1) = qWeight r + (r + 1) := by
  simp [qWeight, Finset.sum_range_succ]
end SharpIntermediateSubgroupBounds
