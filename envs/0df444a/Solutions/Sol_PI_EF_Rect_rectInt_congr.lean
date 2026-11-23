-- Prove2me | solution 1 for PI.EF.Rect.rectInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:57.114782+00:00
-- url     : https://prove2.me/submissions/e50c6533-abb2-44c2-a8ed-0e39231fab17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_hseg_mem_bdry_bot
import Theorems.Thm_PI_EF_Rect_hseg_mem_bdry_top
import Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_left
import Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (rectBdry z w)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_bot hx)),
    intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_left hy))]
end PI.EF.Rect
