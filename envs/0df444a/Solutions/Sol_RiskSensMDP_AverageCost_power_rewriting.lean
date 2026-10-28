-- Prove2me | solution 1 for RiskSensMDP.AverageCost.power_rewriting
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:04:38.664644+00:00
-- url     : https://prove2.me/submissions/74d219ef-bb78-48a4-b530-9f1a49213339

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion
open MeasureTheory ProbabilityTheory Filter Finset

namespace Aux_RSMDP_pow

lemma mul_rpow_pos (x a γ : ℝ) (ha : 0 < a) : (x * a) ^ γ = x ^ γ * a ^ γ := by
  rcases le_or_gt 0 x with hx | hx
  · exact Real.mul_rpow hx ha.le
  · rw [Real.rpow_def_of_neg (mul_neg_of_neg_of_pos hx ha), Real.rpow_def_of_neg hx,
      Real.rpow_def_of_pos ha, Real.log_mul hx.ne ha.ne', add_mul, Real.exp_add]
    ring

end Aux_RSMDP_pow

open RiskSensMDP.AverageCost in
theorem solution {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 0 < γ) (σ : Policy M) (x : E) :
    (∀ n : ℕ, (1 / (n : ℝ)) * (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) =
        (∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)) ∧
    powerAvgCost M γ σ x =
      limsup (fun n : ℕ => (∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)) atTop := by
  have part1 : ∀ n : ℕ, (1 / (n : ℝ)) * (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) =
      (∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, div_zero, zero_mul]
      rw [Real.zero_rpow hγ.ne', integral_zero, Real.zero_rpow (by positivity)]
    · have hnpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      have h1 : ∀ ω, (cost M n ω / n) ^ γ = (cost M n ω) ^ γ * ((n : ℝ)⁻¹) ^ γ := by
        intro ω
        rw [div_eq_mul_inv, Aux_RSMDP_pow.mul_rpow_pos _ _ _ hnpos]
      simp_rw [h1]
      rw [integral_mul_const, Aux_RSMDP_pow.mul_rpow_pos _ _ _ (Real.rpow_pos_of_pos hnpos γ),
        one_div γ, Real.rpow_rpow_inv hnpos.le hγ.ne']
      ring
  refine ⟨part1, ?_⟩
  unfold powerAvgCost
  congr 1
  funext n
  exact part1 n
