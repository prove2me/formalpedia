-- Prove2me | solution 1 for UnifiedFBSDE.Rational.eq_5_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:07:18.53508+00:00
-- url     : https://prove2.me/submissions/200e1a26-f23f-4132-9531-424db88daa4e

import Mathlib
import Definitions.Def_UnifiedFBSDE_Rational_Setting

open UnifiedFBSDE.Rational in
theorem solution (c : Coeffs) (hσ : c.σ₃ ≠ 0) :
    ∃ α₀ α₁ α₂ : ℝ, c.IsDecomp58 α₀ α₁ α₂ := by
  obtain ⟨A, hA'⟩ : ∃ A : ℝ, A * c.σ₃ = -(c.b₃ * c.σ₂) := ⟨_, div_mul_cancel₀ _ hσ⟩
  obtain ⟨B, hB'⟩ : ∃ B : ℝ, B * c.σ₃ = A - c.f₃ * c.σ₂ - c.b₃ * c.σ₁ :=
    ⟨_, div_mul_cancel₀ _ hσ⟩
  obtain ⟨C, hC'⟩ : ∃ C : ℝ, C * c.σ₃ = B - c.f₃ * c.σ₁ := ⟨_, div_mul_cancel₀ _ hσ⟩
  refine ⟨-C / c.σ₃, c.f₁ + C, c.f₂ + c.b₁ + B, ?_⟩
  intro y hy
  have hA : A = -(c.b₃ * c.σ₂) / c.σ₃ := (eq_div_iff hσ).mpr hA'
  have hsplit : 1 / c.σ₃ - y = (1 - c.σ₃ * y) / c.σ₃ := by field_simp
  have hα3 : c.b₂ - c.b₃ * c.σ₂ / c.σ₃ = c.b₂ + A := by rw [hA]; ring
  unfold Coeffs.F
  rw [hsplit, div_div_eq_mul_div, hα3, div_mul_cancel₀ _ hσ]
  rw [eq_comm, ← sub_eq_zero]
  have key : (c.f₃ + c.b₃ * y) * y * (c.σ₁ + c.σ₂ * y) =
      (A * y ^ 2 + B * y + C) * (1 - c.σ₃ * y) - C := by
    linear_combination (y ^ 3) * hA' + (y ^ 2) * hB' + y * hC'
  rw [key]
  field_simp
  ring
