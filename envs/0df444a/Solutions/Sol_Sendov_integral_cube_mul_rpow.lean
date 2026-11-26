-- Prove2me | solution 1 for Sendov.integral_cube_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:18.415224+00:00
-- url     : https://prove2.me/submissions/cd6eaf51-5b89-49ab-8282-385709113837

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_integral_rpow_zero_one
import Theorems.Thm_Sendov_rpow_add_nat_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by
  have h1 : (0 : ℝ) < s + 1 := by linarith
  have hrefl : (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) ^ 3 * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) ^ 3 * x ^ s
        = x ^ s - 3 * x ^ (s + (1 : ℕ)) + 3 * x ^ (s + (2 : ℕ)) - x ^ (s + (3 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]
      rw [Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith),
        Real.zero_rpow (by push_cast; linarith), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h, rpow_add_nat_pos h, rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (s + (m : ℕ))) volume 0 1 := by
    intro m
    apply intervalIntegral.intervalIntegrable_rpow'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc : ∀ (a : ℝ) (m : ℕ),
      IntervalIntegrable (fun x : ℝ => a * x ^ (s + (m : ℕ))) volume 0 1 :=
    fun a m => (hi m).const_mul a
  rw [intervalIntegral.integral_sub ((hi'.sub (hc 3 1)).add (hc 3 2)) (hi 3),
    intervalIntegral.integral_add (hi'.sub (hc 3 1)) (hc 3 2),
    intervalIntegral.integral_sub hi' (hc 3 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring
end Sendov
