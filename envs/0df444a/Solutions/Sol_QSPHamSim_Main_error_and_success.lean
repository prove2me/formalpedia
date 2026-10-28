-- Prove2me | solution 1 for QSPHamSim.Main.error_and_success
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:28:13.230922+00:00
-- url     : https://prove2.me/submissions/a75f78ae-931d-49d0-be26-c2ff4540420a

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

theorem solution (A₁ A₂ C₁ h : ℝ → ℝ) (ε : ℝ)
    (hfirst : ∀ θ : ℝ,
      ‖((A₁ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 2 * ε)
    (hsecond : ∀ θ : ℝ, |A₂ θ - A₁ θ| ≤ 6 * ε) :
    ∀ θ : ℝ,
      ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 8 * ε ∧
      1 - 16 * ε ≤ ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I)‖ ^ 2 ∧
      (8 * ε ≤ 1 →
        (1 - 8 * ε) ^ 2 ≤
          ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I)‖ ^ 2) := by
  intro θ
  let z₁ : ℂ := (A₁ θ : ℂ) + (C₁ θ : ℂ) * Complex.I
  let z₂ : ℂ := (A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I
  let u : ℂ := Complex.exp ((h θ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hdiff : ‖z₂ - z₁‖ ≤ 6 * ε := by
    have heq : z₂ - z₁ = ((A₂ θ - A₁ θ : ℝ) : ℂ) := by
      simp only [z₁, z₂, Complex.ofReal_sub]
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact hsecond θ
  have herr : ‖z₂ - u‖ ≤ 8 * ε := by
    calc
      ‖z₂ - u‖ ≤ ‖z₂ - z₁‖ + ‖z₁ - u‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (z₂ - z₁) (z₁ - u)
      _ ≤ 6 * ε + 2 * ε := add_le_add hdiff (hfirst θ)
      _ = _ := by ring
  have hlower : 1 - 8 * ε ≤ ‖z₂‖ := by
    have ht := norm_sub_norm_le u z₂
    rw [hu, norm_sub_rev] at ht
    linarith
  refine ⟨herr, ?_, ?_⟩
  · nlinarith [sq_nonneg (‖z₂‖ - 1)]
  · intro he
    exact (sq_le_sq₀ (by linarith) (norm_nonneg z₂)).2 hlower

#print axioms solution
