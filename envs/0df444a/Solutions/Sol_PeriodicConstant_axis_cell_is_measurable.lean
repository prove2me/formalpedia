-- Prove2me | solution 1 for PeriodicConstant.axis_cell_is_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/fd4044ab-1ccf-4903-b2e6-b59880dba06e

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
theorem _root_.solution (L : ℝ) (hL : 0 < L) :
    MeasurableSet (axisAlignedCell (d := d) L) := by
  simpa [axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    fundamentalDomain_measurableSet (axisCellBasis (d := d) L hL)
end PeriodicConstant
