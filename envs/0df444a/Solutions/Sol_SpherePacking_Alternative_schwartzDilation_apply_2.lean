-- Prove2me | solution 2 for SpherePacking.Alternative.schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:50:46.85797+00:00
-- url     : https://prove2.me/submissions/a5a4545a-e6e4-4922-9ad2-d5e6309fcd5a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative


theorem solution {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (f : Schwartz d) (x : Ambient d) :
    schwartzDilation a ha f x = f (a • x) := by
  rfl


