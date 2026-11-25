-- Prove2me | solution 1 for PI.EF.Rect.rectInt_eq_zero_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:21.504848+00:00
-- url     : https://prove2.me/submissions/93eafcbe-ffc9-4d71-9a51-9ed24cebb6a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_hint_of_hasDerivAt
import Theorems.Thm_PI_EF_Rect_vint_of_hasDerivAt
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
theorem _root_.solution {F f : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s ∈ rectBdry z w, HasDerivAt F (f s) s) (hc : ∀ s ∈ rectBdry z w, ContinuousAt f s) :
    rectInt f z w = 0 := by
  unfold rectInt
  rw [hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_bot hx)) (fun x hx => hc _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_top hx)) (fun x hx => hc _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_right hy)) (fun y hy => hc _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_left hy)) (fun y hy => hc _ (vseg_mem_bdry_left hy))]
  ring
end PI.EF.Rect
