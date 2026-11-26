-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussian_total_div_primePowerU_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:07.26971+00:00
-- url     : https://prove2.me/submissions/08f8f77d-3fa1-4443-a888-53e3846c168d

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_even_rank_asymptotic
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerU_even_rank_asymptotic
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_pos


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (totalQBinom p (2 * a) : ℝ) / primePowerU p (2 * a)) atTop (nhds 1) := by
  have hdiv := (gaussian_even_rank_asymptotic hp).div
    (primePowerU_even_rank_asymptotic hp)
    (ne_of_gt (sharpConstant_pos (by exact_mod_cast hp)))
  have hCne : sharpConstant (p : ℝ) ≠ 0 :=
    ne_of_gt (sharpConstant_pos (by exact_mod_cast hp))
  rw [div_self hCne] at hdiv
  apply hdiv.congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    have hp0 : (p : ℝ)⁻¹ ^ (a * a) ≠ 0 := by
      exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast (by omega : p ≠ 0)))
    dsimp
    field_simp [hp0]
end SharpIntermediateSubgroupBounds
