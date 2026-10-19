-- Prove2me | solution 1 for SchwartzMap.UnitAddTorus.coordinate_torus_projection_measure_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/174d4064-cf16-468f-8827-7dde9ff75502

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus
namespace SchwartzMap.UnitAddTorus
theorem _root_.solution (n : ℕ) (t : ℝ) :
    MeasurePreserving (coordinateTorusProjection n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
  simpa [coordinateTorusProjection] using!
    (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
      (hf := fun _ => UnitAddCircle.measurePreserving_mk t))
end SchwartzMap.UnitAddTorus
