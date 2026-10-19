-- Prove2me | solution 2 for PeriodicConstantApprox.coordinate_abs_lt_of_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:58.96701+00:00
-- url     : https://prove2.me/submissions/995729c1-b00d-464c-8110-23029f2b4224

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
open PeriodicConstantApprox
open scoped ENNReal Pointwise BigOperators


theorem solution {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hx : ‖x‖ < r)
    (i : Fin d) : |x i| < r := by
  have := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at this
  exact lt_of_le_of_lt this hx

