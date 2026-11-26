-- Prove2me | solution 1 for Sqrt6KissingBound.integral_div_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:11.0545+00:00
-- url     : https://prove2.me/submissions/abc2ac4f-8572-46ac-a303-99f39fa87328

import Mathlib
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open scoped Interval Real
open intervalIntegral
namespace Sqrt6KissingBound
theorem _root_.solution (m : ℕ) {a c : ℝ} (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..a, (t / c) ^ m) =
      a ^ (m + 1) / (c ^ m * (m + 1)) := by
  calc
    (∫ t in (0 : ℝ)..a, (t / c) ^ m) =
        ∫ t in (0 : ℝ)..a, (c ^ m)⁻¹ * t ^ m := by
          apply intervalIntegral.integral_congr
          intro t ht
          change (t / c) ^ m = (c ^ m)⁻¹ * t ^ m
          rw [div_pow]
          simp only [div_eq_mul_inv]
          ring
    _ = (c ^ m)⁻¹ * ∫ t in (0 : ℝ)..a, t ^ m := by
          rw [intervalIntegral.integral_const_mul]
    _ = a ^ (m + 1) / (c ^ m * (m + 1)) := by
          rw [integral_pow]
          simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
            mul_assoc]
end Sqrt6KissingBound
