-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:00.401806+00:00
-- url     : https://prove2.me/submissions/a5a97786-3e41-4653-a65f-2a4ee826e6a7

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
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ normalizedOddGaussianRight p a j := by
  unfold normalizedOddGaussianRight
  split_ifs
  · positivity
  · exact le_rfl
end SharpIntermediateSubgroupBounds
