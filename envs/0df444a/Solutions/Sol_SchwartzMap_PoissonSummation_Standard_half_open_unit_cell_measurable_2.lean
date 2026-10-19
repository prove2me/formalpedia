-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:13.128154+00:00
-- url     : https://prove2.me/submissions/6e5c0c6d-a144-44cc-a928-41f7d6c46d36

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


theorem solution : MeasurableSet (halfOpenUnitCell (d := d)) := by
  have h : halfOpenUnitCell (d := d) = ⋂ i : Fin d, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Set.Ioc 0 1 := by
    ext x; simp [halfOpenUnitCell]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (EuclideanSpace.proj i).continuous.measurable

