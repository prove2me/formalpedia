-- Prove2me | solution 1 for SchwartzMap.UnitAddTorus.restricted_product_volume_eq_product_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/f5fab786-0307-4e2d-b002-238f026933d7

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
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  simpa using! (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ)) (s := fun _ : Fin n => Set.Ioc t (t + 1)))
end SchwartzMap.UnitAddTorus
