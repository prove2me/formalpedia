-- Prove2me | solution 1 for Rudin.ch03_radius_of_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T14:51:11.342741+00:00
-- url     : https://prove2.me/submissions/bf0cac0e-8b24-414b-acf8-f8e3ab17c9d6

import Mathlib
import Definitions.Def_Rudin_ch03_series
import Theorems.Thm_Rudin_ch03_root_test

open Filter Topology

/-- The root of the `n`-th coefficient of the power series is `‖z‖` times that of `cₙ`,
for every `n ≥ 1`. -/
private theorem limsup_root_power_series (c : ℕ → ℂ) (z : ℂ) :
    limsup (fun n => ((‖c n * z ^ n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop
      = (‖z‖ : EReal) * limsup (fun n => ((‖c n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop := by
  have hcongr : (fun n => ((‖c n * z ^ n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal))
      =ᶠ[atTop] fun n => (‖z‖ : EReal) * ((‖c n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : n ≠ 0 := by omega
    have h1 : ‖c n * z ^ n‖ = ‖c n‖ * ‖z‖ ^ n := by
      rw [norm_mul, norm_pow]
    have h2 : (‖c n‖ * ‖z‖ ^ n) ^ ((n : ℝ)⁻¹)
        = ‖c n‖ ^ ((n : ℝ)⁻¹) * (‖z‖ ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.mul_rpow (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)
    have h3 : (‖z‖ ^ n) ^ ((n : ℝ)⁻¹) = ‖z‖ := Real.pow_rpow_inv_natCast (norm_nonneg _) hne
    rw [h1, h2, h3]
    push_cast
    rw [mul_comm]
  rw [limsup_congr hcongr]
  exact EReal.limsup_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (norm_nonneg _))
    (EReal.coe_ne_top _)

/-- Rudin, Theorem 3.39: given the power series `∑ cₙ zⁿ`, put `α = limsup ‖cₙ‖^{1/n}` and
`R = 1/α` (so `R = ∞` when `α = 0` and `R = 0` when `α = ∞`).  Then the series converges when
`‖z‖ < R` and diverges when `‖z‖ > R`.  The two cases are stated here as `α ‖z‖ < 1` and
`α ‖z‖ > 1`, which avoids dividing in the extended reals. -/
theorem solution (c : ℕ → ℂ) (z : ℂ) (α : EReal)
    (hα : α = limsup (fun n => ((‖c n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop) :
    (α * (‖z‖ : EReal) < 1 → Rudin.SeriesConverges fun n => c n * z ^ n) ∧
    (1 < α * (‖z‖ : EReal) → ¬ Rudin.SeriesConverges fun n => c n * z ^ n) := by
  obtain ⟨hconv, hdiv⟩ := Rudin.ch03_root_test (fun n => c n * z ^ n)
  have hlim : limsup (fun n => ((‖c n * z ^ n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop
      = α * (‖z‖ : EReal) := by
    rw [limsup_root_power_series c z, hα, mul_comm]
  rw [hlim] at hconv hdiv
  exact ⟨hconv, hdiv⟩
