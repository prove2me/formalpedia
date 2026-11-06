-- Prove2me | solution 1 for QEC.Locality.addCircle_coe_add_int_mul_period
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:20:24.510701+00:00
-- url     : https://prove2.me/submissions/244163ac-c960-43c1-97e5-085c45b5d44e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

theorem solution (w x : ℝ) (m : ℤ) :
    ((x + (m : ℝ) * w : ℝ) : AddCircle w) = (x : AddCircle w) := by
  rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, add_zero]
