-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_null_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:03.960415+00:00
-- url     : https://prove2.me/submissions/9c4e35b0-d462-4d85-adaa-61de825d569b

import Mathlib
import Definitions.Def_SpherePacking
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


theorem solution : NullMeasurableSet (halfOpenUnitCell (d := d)) := by
  apply MeasurableSet.nullMeasurableSet
  have : halfOpenUnitCell (d := d) = ⋂ i : Fin d, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Set.Ioc (0:ℝ) 1 := by
    ext x; simp [halfOpenUnitCell]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

