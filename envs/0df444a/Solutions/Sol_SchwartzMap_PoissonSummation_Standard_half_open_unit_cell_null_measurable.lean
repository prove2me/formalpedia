-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_null_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/bdf1fb19-fd07-482e-8269-1f3c1033e5b8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_measurable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators
open MeasureTheory
open SchwartzMap
open TopologicalSpace MeasureTheory
variable {d : ℕ}
open SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
open UnitAddTorus
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution : NullMeasurableSet (halfOpenUnitCell (d := d)) :=
  (half_open_unit_cell_measurable (d := d)).nullMeasurableSet
end SchwartzMap.PoissonSummation.Standard
