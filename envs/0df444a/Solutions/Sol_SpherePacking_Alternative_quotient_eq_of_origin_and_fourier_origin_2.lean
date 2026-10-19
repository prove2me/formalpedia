-- Prove2me | solution 2 for SpherePacking.Alternative.quotient_eq_of_origin_and_fourier_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:25.850005+00:00
-- url     : https://prove2.me/submissions/f46f6b5b-a784-4c9a-a93a-5297de583d7e

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


theorem solution
    {d : ℕ} {f g : Schwartz d}
    (horigin : g 0 = f 0)
    (hfourier : fourierReal g 0 = fourierReal f 0) :
    quotient g = quotient f := by
  unfold SpherePacking.Alternative.quotient
  rw [horigin, hfourier]

