-- Prove2me | solution 1 for RybinAI2026.P01.j_closed_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T07:30:28.263876+00:00
-- url     : https://prove2.me/submissions/5deff474-2016-4600-8cab-da2003e8adcf

-- DRAFT FRAGMENT — NOT a candidate, NEVER submit as-is.
-- Helper for future RybinAI2026.P01.h_sq_strict_concave candidate (target pending
-- publication). Closed form j(c) = arctan(sqrt c)/sqrt c for c > 0.
-- Every lemma name below was verified present in pinned rev c5ea003 on 2026-10-05:
-- intervalIntegral.integral_comp_mul_left, intervalIntegral.integral_inv_one_add_sq
-- (@[simp]), Real.sq_sqrt, Real.sqrt_pos, Real.arctan_zero.
-- Remote verification still required after integration into the full proof.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

-- j(c) closed form for c > 0 (Step 1 of l2c_proof_SKELETON.md).
theorem solution (c : ℝ) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1, ((1 : ℝ) + c * t ^ 2)⁻¹)
      = Real.arctan (Real.sqrt c) / Real.sqrt c := by
  have hsq2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  have hsqne : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have e : (fun t : ℝ => ((1 : ℝ) + c * t ^ 2)⁻¹)
      = fun t : ℝ => ((1 : ℝ) + (Real.sqrt c * t) ^ 2)⁻¹ := by
    funext t
    rw [mul_pow, hsq2]
  rw [e, integral_comp_mul_left (f := fun s : ℝ => ((1 : ℝ) + s ^ 2)⁻¹) hsqne,
    integral_inv_one_add_sq]
  simp [Real.arctan_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
