-- Prove2me | solution 1 for Sendov.integral_lin_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:16.628818+00:00
-- url     : https://prove2.me/submissions/532a0060-b5d7-4df9-8bfe-b8e3da5bcfd2

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_integral_rpow_zero_one
import Theorems.Thm_Sendov_rpow_add_nat_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s) = 1 / ((s + 1) * (s + 2)) := by
  have hrefl : (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) * x ^ s = x ^ s - x ^ (s + (1 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (s + (1 : ℕ))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_rpow'
    push_cast
    linarith
  rw [intervalIntegral.integral_sub hi' hi, integral_rpow_zero_one (by linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring
end Sendov
