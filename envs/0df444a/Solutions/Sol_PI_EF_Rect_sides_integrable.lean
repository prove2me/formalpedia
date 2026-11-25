-- Prove2me | solution 1 for PI.EF.Rect.sides_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:55.399582+00:00
-- url     : https://prove2.me/submissions/f6e61785-c282-4913-9a7f-d2415d96ba84

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
theorem _root_.solution {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousOn
      fun x hx => hseg_mem_bdry_bot hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousOn
      fun x hx => hseg_mem_bdry_top hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_right hy).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_left hy).intervalIntegrable
end PI.EF.Rect
