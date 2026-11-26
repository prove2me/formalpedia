-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gaussian_even_rank_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:29.985977+00:00
-- url     : https://prove2.me/submissions/caad729d-e630-486e-bf8a-45f6fbb447b9

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_nonneg
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_le
import Theorems.Thm_SharpIntermediateSubgroupBounds_evenGaussianSummand_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_nat_gaussian_inv_pow
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenGaussianSummand_eq_normalized_total
import Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenGaussianLimitSummand_eq_sharpConstant

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  rw [← tsum_evenGaussianLimitSummand_eq_sharpConstant hp]
  have hbound : Summable (fun j : ℕ ↦
      2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j)) :=
    (summable_nat_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, evenGaussianSummand p a j) atTop
      (nhds (∑' j : ℕ, evenGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence
      (f := fun a j ↦ evenGaussianSummand p a j)
      (g := fun j ↦ evenGaussianLimitSummand p j)
      (bound := fun j ↦ 2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j))
      hbound (fun j ↦ evenGaussianSummand_tendsto hp)
      (Filter.Eventually.of_forall fun a j ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · calc
            evenGaussianSummand p a j ≤
                2 * normalizedGaussianRight p a j := by
              have hn := normalizedGaussianRight_nonneg (p := p) (a := a) (j := j) hp
              unfold evenGaussianSummand centerMultiplicity
              by_cases hj : j = 0
              · simp only [if_pos hj, Nat.cast_one, one_mul]
                linarith
              · rw [if_neg hj]
                change (2 : ℝ) * normalizedGaussianRight p a j ≤
                    2 * normalizedGaussianRight p a j
                exact le_rfl
            _ ≤ 2 * (eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j)) := by
              gcongr
              exact normalizedGaussianRight_le hp
            _ = 2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by ring
        · exact mul_nonneg (by positivity) (normalizedGaussianRight_nonneg hp))
  exact ht.congr' (Filter.Eventually.of_forall fun a ↦
    tsum_evenGaussianSummand_eq_normalized_total hp)
end SharpIntermediateSubgroupBounds
