-- Prove2me | solution 1 for RobustPower.StochGap.p14_mean_policy_feasible_for_symmetry_scenario
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:41:53.751902+00:00
-- url     : https://prove2.me/submissions/c97ee1e7-1af5-4584-a7d0-5aaefae6a076

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems

set_option autoImplicit false

open MeasureTheory Matrix RobustPower.StochGap in
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (hbint : Integrable b μ) (ω₀ : Ω)
    (hmean : b ω₀ ≤ ∫ ω, b ω ∂μ)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (hyint : Integrable y μ) (hy : ∀ ω, 0 ≤ y ω)
    (hfeas : ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y ω) :
    0 ≤ ∫ ω, y ω ∂μ ∧ b ω₀ ≤ A *ᵥ x + B *ᵥ (∫ ω, y ω ∂μ) := by
  have hyi : ∀ j, Integrable (fun ω => y ω j) μ := hyint.eval
  have hbi : ∀ i, Integrable (fun ω => b ω i) μ := hbint.eval
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [Pi.zero_apply, eval_integral hyi]
    exact integral_nonneg (fun ω => hy ω j)
  · have h1 := hmean i
    rw [eval_integral hbi] at h1
    have key : (B *ᵥ ∫ ω, y ω ∂μ) i = ∫ ω, (B *ᵥ y ω) i ∂μ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [integral_finsetSum _ (fun j _ => (hyi j).const_mul (B i j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [eval_integral hyi, integral_const_mul]
    have hint : Integrable (fun ω => (B *ᵥ y ω) i) μ := by
      simp only [Matrix.mulVec, dotProduct]
      exact integrable_finsetSum _ (fun j _ => (hyi j).const_mul (B i j))
    calc b ω₀ i ≤ ∫ ω, b ω i ∂μ := h1
      _ ≤ ∫ ω, ((A *ᵥ x) i + (B *ᵥ y ω) i) ∂μ :=
          integral_mono (hbi i) ((integrable_const _).add hint) (fun ω => hfeas ω i)
      _ = (A *ᵥ x + B *ᵥ (∫ ω, y ω ∂μ)) i := by
          rw [integral_add (integrable_const _) hint, integral_const, ← key]
          simp
