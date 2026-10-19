-- Prove2me | solution 1 for SpherePacking.Alternative.schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/08a9b286-2814-45c7-be3a-713b99d690b5

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
theorem _root_.solution {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (f : Schwartz d) (x : Ambient d) :
    schwartzDilation a ha f x = f (a • x) := by
  rfl
end SpherePacking.Alternative
