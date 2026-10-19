-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/05b718a4-d0e7-495e-baae-7a3d3002dbaa

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution : MeasurableSet (halfOpenUnitCell (d := d)) := by
  have hset :
      halfOpenUnitCell (d := d) = ⋂ i : Fin d, {x : (EuclideanSpace ℝ (Fin d)) | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    ext x
    simp [halfOpenUnitCell]
  have hcoord :
      ∀ i : Fin d, MeasurableSet {x : (EuclideanSpace ℝ (Fin d)) | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    intro i
    have hproj : Measurable fun x : (EuclideanSpace ℝ (Fin d)) => x i := by
      simpa using!
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ) i).measurable
    exact hproj measurableSet_Ioc
  simpa [hset] using! MeasurableSet.iInter (ι := Fin d) hcoord
end SchwartzMap.PoissonSummation.Standard
