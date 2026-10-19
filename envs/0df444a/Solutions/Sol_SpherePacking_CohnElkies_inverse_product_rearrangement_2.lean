-- Prove2me | solution 2 for SpherePacking.CohnElkies.inverse_product_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:00:24.026064+00:00
-- url     : https://prove2.me/submissions/ef1cbde6-0675-4bad-8b7c-e3c230a02099

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies


theorem solution {α : Type*} [DivisionCommMonoid α] (c a b : α) :
    (1 / c) * a * b = b * a / c := by
  rw [one_div, div_eq_mul_inv, mul_comm b a, mul_comm _ a, mul_assoc, mul_comm]
  simp only [mul_assoc, mul_comm, mul_left_comm]

