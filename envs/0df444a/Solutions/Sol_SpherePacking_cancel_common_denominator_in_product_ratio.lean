-- Prove2me | solution 1 for SpherePacking.cancel_common_denominator_in_product_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/673a33fb-4f21-4926-a39d-5db626399b63

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open SpherePacking
open Filter
open scoped ENNReal BigOperators
variable {d : ℕ}
namespace SpherePacking
theorem _root_.solution {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞) :
    ((a * b) / c) / b = a / c := by
  calc
    ((a * b) / c) / b = (a * b) * c⁻¹ * b⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = a * c⁻¹ * (b * b⁻¹) := by
      ac_rfl
    _ = a / c := by
      simp [div_eq_mul_inv, ENNReal.mul_inv_cancel hb0 hb]
end SpherePacking
