-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussian_odd_rank_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:43.832795+00:00
-- url     : https://prove2.me/submissions/20ab4fb5-f0f2-46cc-a2dc-93fcb88ef53a

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianSummand_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_nat_odd_gaussian_inv_pow
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_oddGaussianSummand_eq_normalized_total
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_oddGaussianLimitSummand_eq_oddGaussianConstant
import Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianSummand_nonneg
import Theorems.Thm_SharpIntermediateSubgroupBounds_oddGaussianSummand_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by
  rw [← tsum_oddGaussianLimitSummand_eq_oddGaussianConstant hp]
  have hbound : Summable (fun j : ℕ ↦
      2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
        (p : ℝ)⁻¹ ^ (j * (j + 1))) :=
    (summable_nat_odd_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, oddGaussianSummand p a j)
      atTop (nhds (∑' j : ℕ, oddGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence hbound
      (fun j : ℕ ↦ oddGaussianSummand_tendsto hp)
      (Filter.Eventually.of_forall fun (a j : ℕ) ↦ ?_)
  · convert ht using 1
    funext a
    exact (tsum_oddGaussianSummand_eq_normalized_total (a := a) hp).symm
  · rw [Real.norm_eq_abs, abs_of_nonneg (oddGaussianSummand_nonneg hp)]
    exact oddGaussianSummand_le hp
end SharpIntermediateSubgroupBounds
