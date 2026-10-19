-- Prove2me | solution 2 for SchwartzMap.UnitAddTorus.restricted_product_volume_eq_product_restriction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:34.254655+00:00
-- url     : https://prove2.me/submissions/3a1a4dae-5d05-4144-9c73-981fe72c5c8a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus


theorem solution (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]

