-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.sharpConstant_le_of_even_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:09.910904+00:00
-- url     : https://prove2.me/submissions/b5a04a48-8095-40b0-9d94-66fb9ffd6cd9

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_even_rank_asymptotic

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {C : ℝ}
    (hC : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C :=
  le_of_tendsto (gaussian_even_rank_asymptotic hp) (Filter.Eventually.of_forall hC)
end SharpIntermediateSubgroupBounds
