-- Prove2me | solution 1 for QuantumNoise.optimal_cross_correlation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:10:02.871346+00:00
-- url     : https://prove2.me/submissions/1eacf8a0-b443-41df-a9d4-3c5d8e6c0078

import Mathlib

namespace Aux_QuantumNoise_occ

theorem key (A u w r : ℝ) (huw : u ^ 2 + w ^ 2 = 1) :
    A * u + w * r ≤ Real.sqrt (A ^ 2 + r ^ 2) := by
  have h : (A * u + w * r) ^ 2 ≤ A ^ 2 + r ^ 2 := by
    nlinarith [sq_nonneg (A * w - r * u)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

theorem eq_iff (A u w r : ℝ) (hA : 0 < A) (hu : 0 < u) (huw : u ^ 2 + w ^ 2 = 1) :
    Real.sqrt (A ^ 2 + r ^ 2) = A * u + w * r ↔ r = A * w / u := by
  constructor
  · intro h
    have hnn : 0 ≤ A * u + w * r := h ▸ Real.sqrt_nonneg _
    have h2 : A ^ 2 + r ^ 2 = (A * u + w * r) ^ 2 := by
      rw [← h, Real.sq_sqrt (by positivity)]
    have h3 : (A * w - r * u) ^ 2 = 0 := by nlinarith
    have h4 : A * w - r * u = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    field_simp
    linarith
  · intro h
    have hval : A * u + w * r = A / u := by
      rw [h]; field_simp; nlinarith
    have hsq : A ^ 2 + r ^ 2 = (A / u) ^ 2 := by
      rw [h]; field_simp; nlinarith
    rw [hval, hsq, Real.sqrt_sq (by positivity)]

end Aux_QuantumNoise_occ

theorem solution (ħ : ℝ) (hħ : 0 < ħ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (χ : ℂ)
    (hχ : χ.im ≠ 0) :
    (∀ r : ℝ, ħ * |χ.im| ≤
        2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + r ^ 2) + σ * Real.cos (Complex.arg χ) * r)) ∧
      ∀ r : ℝ, 2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + r ^ 2) + σ * Real.cos (Complex.arg χ) * r) =
          ħ * |χ.im| ↔
        r = -σ * (ħ / 2) * Real.cos (Complex.arg χ) / |Real.sin (Complex.arg χ)| := by
  have hχ0 : χ ≠ 0 := by rintro rfl; simp at hχ
  have hρ : 0 < ‖χ‖ := norm_pos_iff.mpr hχ0
  have him : χ.im = ‖χ‖ * Real.sin (Complex.arg χ) := (Complex.norm_mul_sin_arg χ).symm
  have habs : |χ.im| = ‖χ‖ * |Real.sin (Complex.arg χ)| := by
    rw [him, abs_mul, abs_of_pos hρ]
  have hs0 : Real.sin (Complex.arg χ) ≠ 0 := by
    intro h; apply hχ; rw [him, h, mul_zero]
  have hu : 0 < |Real.sin (Complex.arg χ)| := abs_pos.mpr hs0
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have huw : |Real.sin (Complex.arg χ)| ^ 2 + (-σ * Real.cos (Complex.arg χ)) ^ 2 = 1 := by
    rw [sq_abs]
    have := Real.sin_sq_add_cos_sq (Complex.arg χ)
    nlinarith
  have hA : 0 < ħ / 2 := by positivity
  rw [habs]
  constructor
  · intro r
    have := Aux_QuantumNoise_occ.key (ħ / 2) |Real.sin (Complex.arg χ)|
      (-σ * Real.cos (Complex.arg χ)) r huw
    have h2 := mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * ‖χ‖ by positivity)
    nlinarith
  · intro r
    have hre : -σ * (ħ / 2) * Real.cos (Complex.arg χ) / |Real.sin (Complex.arg χ)| =
        ħ / 2 * (-σ * Real.cos (Complex.arg χ)) / |Real.sin (Complex.arg χ)| := by ring
    rw [hre, ← Aux_QuantumNoise_occ.eq_iff (ħ / 2) |Real.sin (Complex.arg χ)|
      (-σ * Real.cos (Complex.arg χ)) r hA hu huw]
    constructor
    · intro h
      have h2 : 2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + r ^ 2)) =
          2 * ‖χ‖ * (ħ / 2 * |Real.sin (Complex.arg χ)| + -σ * Real.cos (Complex.arg χ) * r) := by
        linarith
      exact mul_left_cancel₀ (by positivity) h2
    · intro h
      rw [h]; ring
