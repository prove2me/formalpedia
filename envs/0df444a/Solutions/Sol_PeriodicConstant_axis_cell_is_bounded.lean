-- Prove2me | solution 1 for PeriodicConstant.axis_cell_is_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/e2ba57e7-dfdc-4a12-b572-c88747134c5a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open PeriodicConstant
variable {d : ℕ}
namespace PeriodicConstant
theorem _root_.solution (L : ℝ) (hL : 0 < L) : IsBounded (axisAlignedCell (d := d) L) := by
  simpa [axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    fundamentalDomain_isBounded (axisCellBasis (d := d) L hL)
end PeriodicConstant
