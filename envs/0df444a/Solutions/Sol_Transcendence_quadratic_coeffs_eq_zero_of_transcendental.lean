-- Prove2me | solution 1 for Transcendence.quadratic_coeffs_eq_zero_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:35:13.952438+00:00
-- url     : https://prove2.me/submissions/750283d2-77b7-4fcb-836e-cc0af49439a1

import Mathlib

namespace S7W2_quadratic_coeffs_eq_zero_of_transcendental

/-- Rationals are algebraic over `ℚ`. -/
theorem isAlg_rat (q : ℚ) : IsAlgebraic ℚ (q : ℂ) := isAlgebraic_algebraMap q

end S7W2_quadratic_coeffs_eq_zero_of_transcendental

open S7W2_quadratic_coeffs_eq_zero_of_transcendental in
/- If `c₂ ≠ 0`, completing the square gives `(2c₂x + c₁)² = c₁² − 4c₂c₀`, so `2c₂x + c₁` and then
`x` are algebraic. If `c₂ = 0` and `c₁ ≠ 0`, then `x = −c₀/c₁` is algebraic. Both contradict the
transcendence of `x`, and then `c₀ = 0`. -/
theorem solution {x c₀ c₁ c₂ : ℂ} (hx : Transcendental ℚ x)
    (h₀ : IsAlgebraic ℚ c₀) (h₁ : IsAlgebraic ℚ c₁) (h₂ : IsAlgebraic ℚ c₂)
    (h : c₂ * x ^ 2 + c₁ * x + c₀ = 0) :
    c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  have h2 : IsAlgebraic ℚ (2 : ℂ) := by exact_mod_cast isAlg_rat 2
  have h4 : IsAlgebraic ℚ (4 : ℂ) := by exact_mod_cast isAlg_rat 4
  have hc₂ : c₂ = 0 := by
    by_contra hc₂
    apply hx
    have hs : IsAlgebraic ℚ (2 * c₂ * x + c₁) := by
      refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
      rw [show (2 * c₂ * x + c₁) ^ 2 = c₁ ^ 2 - 4 * c₂ * c₀ by linear_combination 4 * c₂ * h]
      exact (h₁.pow 2).sub ((h4.mul h₂).mul h₀)
    have hx' : x = (2 * c₂ * x + c₁ - c₁) * (2 * c₂)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (mul_ne_zero two_ne_zero hc₂)]
      ring
    rw [hx']
    exact (hs.sub h₁).mul (h2.mul h₂).inv
  have hc₁ : c₁ = 0 := by
    by_contra hc₁
    apply hx
    have hx' : x = -c₀ * c₁⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hc₁]
      linear_combination h - x ^ 2 * hc₂
    rw [hx']
    exact h₀.neg.mul h₁.inv
  exact ⟨hc₂, hc₁, by linear_combination h - x ^ 2 * hc₂ - x * hc₁⟩

#print axioms solution
