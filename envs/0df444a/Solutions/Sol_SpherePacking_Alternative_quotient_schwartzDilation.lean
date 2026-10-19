-- Prove2me | solution 1 for SpherePacking.Alternative.quotient_schwartzDilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/b4b9ea1e-664c-4abd-bff0-e4f78f124f4d

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
theorem _root_.solution {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) :
    quotient (schwartzDilation a ha.ne' f) =
      a ^ d * quotient f := by
  unfold quotient
  rw [schwartzDilation_zero,
    fourierReal_schwartzDilation_apply a ha f 0]
  simp only [smul_zero]
  have hpow : a ^ d ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp
end SpherePacking.Alternative
