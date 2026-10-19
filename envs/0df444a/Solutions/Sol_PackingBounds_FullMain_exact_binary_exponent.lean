-- Prove2me | solution 1 for PackingBounds.FullMain.exact_binary_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/231890c3-7a92-4e94-8330-6bca808f6d4a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_RadialMain_exact_binary_exponent
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
import Theorems.Thm_PackingBounds_fullLinearProgram_eq_radial
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
open Filter
open scoped FourierTransform SchwartzMap Topology
open PackingBounds
open PackingBounds.FullMain
namespace PackingBounds.FullMain
theorem _root_.solution :
    Tendsto
      (fun d : ℕ =>
        Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (nhds (-(1 / 2 : ℝ) *
        Real.logb 2 (2 * Real.pi / Real.exp 1))) := by
  simpa only [fullLinearProgram_eq_radial] using
    RadialMain.exact_binary_exponent
end PackingBounds.FullMain
