-- Prove2me | solution 1 for SpherePacking.Alternative.quotient_eq_of_origin_and_fourier_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/4dbc8b95-c957-4dff-bb6d-84c1425248b8

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
namespace SpherePacking.Alternative
theorem _root_.solution
    {d : ℕ} {f g : Schwartz d}
    (horigin : g 0 = f 0)
    (hfourier : fourierReal g 0 = fourierReal f 0) :
    quotient g = quotient f := by
  simp only [quotient, horigin, hfourier]
end SpherePacking.Alternative
