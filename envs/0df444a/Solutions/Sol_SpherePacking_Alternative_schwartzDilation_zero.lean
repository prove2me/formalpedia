-- Prove2me | solution 1 for SpherePacking.Alternative.schwartzDilation_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/ca8a2f4e-e214-4046-b35b-f20ac6d918dc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_apply

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
    (f : Schwartz d) :
    schwartzDilation a ha f 0 = f 0 := by
  simp [schwartzDilation_apply]
end SpherePacking.Alternative
