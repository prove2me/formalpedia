-- Prove2me | solution 2 for SpherePacking.cancel_common_denominator_in_product_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:10.970995+00:00
-- url     : https://prove2.me/submissions/9db651f8-9353-4c42-a73a-e8efc2fb844f

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


theorem solution {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞) :
    ((a * b) / c) / b = a / c := by
  rw [ENNReal.mul_div_right_comm, ENNReal.mul_div_cancel_right hb0 hb]

