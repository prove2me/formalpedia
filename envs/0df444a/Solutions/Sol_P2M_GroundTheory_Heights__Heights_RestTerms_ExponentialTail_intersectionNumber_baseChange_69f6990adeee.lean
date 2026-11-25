-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ExponentialTail_intersectionNumber_baseChange_69f6990adeee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:59.295205+00:00
-- url     : https://prove2.me/submissions/9f1b7d31-2ddf-4d8f-8204-7dc005039144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_exp_three_eighths_le_4aa04d42a7fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace ExponentialTail
theorem _root_.solution : ExponentialTail.Statement := by
  intro p X hp hX hXp
  set u : ℝ := X / p with hu
  have hu0 : 0 ≤ u := by positivity
  have hu38 : u ≤ 3 / 8 := by rw [hu, div_le_iff₀ hp]; linarith
  have hA : 0 ≤ X / p ^ 2 := by positivity
  have hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) =
      X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ))) := by
    intro k
    rw [hu, div_pow]
    field_simp
    ring
  have hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
    intro k
    have h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial := by
      have : 2 * k.factorial ≤ (k + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
      X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_eq_mul_one_div (u ^ k)]
    exact mul_le_mul_of_nonneg_left (hfac k) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) := by
    intro k; positivity
  have hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ))) := hexp.mul_left _
  have hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hbound hsum
  refine ⟨hS, ?_, ?_⟩
  · calc ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)
        ≤ ∑' k : ℕ, X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := hS.tsum_le_tsum hbound hsum
      _ = X / p ^ 2 * Real.exp u := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      _ ≤ X / p ^ 2 * Real.exp (3 / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA
      _ = Real.exp (3 / 8) * X / p ^ 2 := by ring
  · have := exp_three_eighths_le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this hA
end ExponentialTail
end GroundTheory.Heights₂.Heights.RestTerms
