-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.no_vanishing_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:13.189131+00:00
-- url     : https://prove2.me/submissions/f7aa2002-4862-4f28-a041-014e0850a8ee

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_even_rank_asymptotic
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_pos


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds 0))
    (hbound : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤ b a) : False := by
  have hle : sharpConstant (p : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto (gaussian_even_rank_asymptotic hp) hb
      (Filter.Eventually.of_forall hbound)
  exact (not_le_of_gt (sharpConstant_pos (by exact_mod_cast hp))) hle
end SharpIntermediateSubgroupBounds
