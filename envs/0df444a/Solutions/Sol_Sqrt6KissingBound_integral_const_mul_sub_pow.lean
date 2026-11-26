-- Prove2me | solution 1 for Sqrt6KissingBound.integral_const_mul_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:20.656273+00:00
-- url     : https://prove2.me/submissions/2fb9fbfb-35cf-4907-be4e-c3a5273a1b0c

import Mathlib
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open scoped Interval Real
open intervalIntegral
namespace Sqrt6KissingBound
theorem _root_.solution (m : ℕ) {a b c : ℝ} :
    (∫ t in a..b, (c * (b - t)) ^ m) =
      c ^ m * (b - a) ^ (m + 1) / (m + 1) := by
  calc
    (∫ t in a..b, (c * (b - t)) ^ m) =
        ∫ t in a..b, c ^ m * (b - t) ^ m := by
          apply intervalIntegral.integral_congr
          intro t ht
          change (c * (b - t)) ^ m = c ^ m * (b - t) ^ m
          rw [mul_pow]
    _ = c ^ m * ∫ t in a..b, (b - t) ^ m := by
          rw [intervalIntegral.integral_const_mul]
    _ = c ^ m * (b - a) ^ (m + 1) / (m + 1) := by
          rw [intervalIntegral.integral_comp_sub_left
            (fun x : ℝ => x ^ m) b]
          rw [integral_pow]
          ring_nf
end Sqrt6KissingBound
