-- Prove2me | solution 1 for PeriodicConstantApprox.coordinate_abs_lt_of_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/e31b96c3-dd05-4af5-beb3-207732e5bdae

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_coordinate_abs_bounded_by_norm

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
namespace PeriodicConstantApprox
theorem _root_.solution {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hx : ‖x‖ < r)
    (i : Fin d) : |x i| < r :=
  lt_of_le_of_lt (coordinate_abs_bounded_by_norm (d := d) x i) hx
end PeriodicConstantApprox
