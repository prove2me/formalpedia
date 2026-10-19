-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_volume_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/c83bb0d7-2b42-4d3e-a223-080958dd8c3e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_half_open_unit_cell_subset_closed_ball

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) < ⊤ := by
  simpa using! ((Metric.isBounded_closedBall (x := (0 : (EuclideanSpace ℝ (Fin d)))) (r := Real.sqrt d)).subset
    (half_open_unit_cell_subset_closed_ball (d := d))).measure_lt_top
end SchwartzMap.PoissonSummation.Standard
