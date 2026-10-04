-- Prove2me | solution 1 for RybinAI2026.P01.psi_ge_log_inv_of_lt_one_r16
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:54:43.689991+00:00
-- url     : https://prove2.me/submissions/542023ba-122a-48ba-9c21-26b12820ff74

import Mathlib

/-! Disproof of e5d0e85f `RybinAI2026.P01.psi_ge_log_inv_of_lt_one_r16`.

With `a = sqrt (1 - t)` the integral equals `artanh a / a = (1/(2a)) log ((1+a)/(1-a))`, which is
about `(1/2) log (4/t)` for small `t`, below `log (1/t)`.  Witness `t = 199/10000`, `a = 99/100`:
the integral is `(50/99) log 199 ≈ 2.67`, while `log (10000/199) ≈ 3.92`. -/

set_option autoImplicit false

open MeasureTheory

namespace PsiCexE5

/-- The value of the integral at `t = 199/10000`. -/
theorem integral_eq :
    (∫ s in (0 : ℝ)..1, (1 + ((199 / 10000 : ℝ) - 1) * s ^ 2)⁻¹)
      = (50 / 99 : ℝ) * Real.log 199 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (50 / 99 : ℝ) *
          (Real.log (1 + 99 / 100 * s) - Real.log (1 - 99 / 100 * s)))
        ((1 + ((199 / 10000 : ℝ) - 1) * x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hp : (0 : ℝ) < 1 + 99 / 100 * x := by linarith
    have hm : (0 : ℝ) < 1 - 99 / 100 * x := by linarith
    have h1 : HasDerivAt (fun s : ℝ => 1 + 99 / 100 * s) (99 / 100) x := by
      simpa using ((hasDerivAt_id x).const_mul (99 / 100 : ℝ)).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => 1 - 99 / 100 * s) (-(99 / 100)) x := by
      simpa using ((hasDerivAt_id x).const_mul (99 / 100 : ℝ)).const_sub 1
    have h3 : HasDerivAt (fun s : ℝ => (50 / 99 : ℝ) *
          (Real.log (1 + 99 / 100 * s) - Real.log (1 - 99 / 100 * s)))
        ((50 / 99 : ℝ) * (99 / 100 / (1 + 99 / 100 * x) - -(99 / 100) / (1 - 99 / 100 * x))) x :=
      ((h1.log hp.ne').sub (h2.log hm.ne')).const_mul (50 / 99 : ℝ)
    refine h3.congr_deriv ?_
    have hfac : 1 + ((199 / 10000 : ℝ) - 1) * x ^ 2 = (1 + 99 / 100 * x) * (1 - 99 / 100 * x) := by
      ring
    have hp' : (1 + 99 / 100 * x : ℝ) ≠ 0 := hp.ne'
    have hm' : (1 - 99 / 100 * x : ℝ) ≠ 0 := hm.ne'
    have hAB : (1 + 99 / 100 * x : ℝ) + (1 - 99 / 100 * x) = 2 := by ring
    rw [hfac]
    generalize (1 + 99 / 100 * x : ℝ) = A at hp' hAB ⊢
    generalize (1 - 99 / 100 * x : ℝ) = B at hm' hAB ⊢
    have hk : (50 / 99 : ℝ) * (99 / 100 / A - -(99 / 100) / B) = (A + B) / (2 * (A * B)) := by
      field_simp
      ring
    rw [hk, hAB]
    field_simp
  have hcont : ContinuousOn (fun x : ℝ => (1 + ((199 / 10000 : ℝ) - 1) * x ^ 2)⁻¹)
      (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have : x ^ 2 ≤ 1 := by nlinarith
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have e1 : Real.log (1 + 99 / 100 * (1 : ℝ)) - Real.log (1 - 99 / 100 * 1)
      = Real.log 199 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  simp only [mul_zero, add_zero, sub_zero, Real.log_one, sub_self]
  rw [e1]

theorem cex : ¬ (∀ (t : ℝ), 0 < t → t < 1 →
    (Real.log (1 / t)) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) := by
  intro h
  have h0 := h (199 / 10000) (by norm_num) (by norm_num)
  rw [integral_eq] at h0
  have hL1 : 0 < Real.log 199 := Real.log_pos (by norm_num)
  have hcmp := Real.log_le_log (by norm_num)
    (show (199 : ℝ) ^ 2 ≤ (1 / (199 / 10000 : ℝ)) ^ 3 by norm_num)
  rw [Real.log_pow, Real.log_pow] at hcmp
  push_cast at hcmp
  linarith

end PsiCexE5

theorem solution : ¬ (∀ (t : ℝ), 0 < t → t < 1 →
    (Real.log (1 / t)) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) := by
  exact PsiCexE5.cex
