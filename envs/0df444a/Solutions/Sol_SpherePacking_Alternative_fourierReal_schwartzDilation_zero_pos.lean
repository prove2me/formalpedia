-- Prove2me | solution 1 for SpherePacking.Alternative.fourierReal_schwartzDilation_zero_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/7eaa98ae-0268-4e2a-8a40-3a8bccb2db9a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
import Theorems.Thm_SpherePacking_Alternative_fourierReal_schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_zero

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
theorem _root_.solution {d : ℕ}
    {f : Schwartz d} (hf : 0 < fourierReal f 0)
    (a : ℝ) (ha : 0 < a) :
    0 < fourierReal (schwartzDilation a ha.ne' f) 0 := by
  rw [fourierReal_schwartzDilation_apply a ha f 0]
  simp only [smul_zero]
  exact mul_pos (by positivity) hf
end SpherePacking.Alternative
