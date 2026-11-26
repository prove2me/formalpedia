-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.primePowerU_even_rank_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:16.643295+00:00
-- url     : https://prove2.me/submissions/3baaf7bf-6196-4a54-a1d0-e9b0cd3601af

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_nat_gaussian_inv_pow
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenGaussianLimitSummand_eq_sharpConstant
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenUSummand_eq_normalized_U
import Theorems.Thm_SharpIntermediateSubgroupBounds_evenUSummand_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_evenUSummand_nonneg
import Theorems.Thm_SharpIntermediateSubgroupBounds_evenUSummand_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  rw [← tsum_evenGaussianLimitSummand_eq_sharpConstant hp]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbound : Summable (fun j : ℕ ↦
      2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)) :=
    (summable_nat_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, evenUSummand p a j) atTop
      (nhds (∑' j : ℕ, evenGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence
      (f := fun a j ↦ evenUSummand p a j)
      (g := fun j ↦ evenGaussianLimitSummand p j)
      (bound := fun j ↦ 2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))
      hbound (fun j ↦ evenUSummand_tendsto hp)
      (Filter.Eventually.of_forall fun a j ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (evenUSummand_nonneg hp)]
        exact evenUSummand_le hp)
  exact ht.congr' (Filter.Eventually.of_forall fun a ↦
    tsum_evenUSummand_eq_normalized_U hp)
end SharpIntermediateSubgroupBounds
