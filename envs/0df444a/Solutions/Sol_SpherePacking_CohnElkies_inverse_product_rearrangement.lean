-- Prove2me | solution 1 for SpherePacking.CohnElkies.inverse_product_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/4dda4054-1fa8-45e1-806a-b79809ab2e7e

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies
namespace SpherePacking.CohnElkies
theorem _root_.solution {α : Type*} [DivisionCommMonoid α] (c a b : α) :
    (1 / c) * a * b = b * a / c := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
end SpherePacking.CohnElkies
