-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianRight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:27.860336+00:00
-- url     : https://prove2.me/submissions/506b0acf-4e04-4e29-86bf-f58e970aed71

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
    0 ≤ normalizedGaussianRight p a j := by
  unfold normalizedGaussianRight
  split_ifs
  · positivity
  · exact le_rfl
end SharpIntermediateSubgroupBounds
