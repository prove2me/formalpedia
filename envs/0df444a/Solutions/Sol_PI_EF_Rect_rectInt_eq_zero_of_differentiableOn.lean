-- Prove2me | solution 1 for PI.EF.Rect.rectInt_eq_zero_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:45.260395+00:00
-- url     : https://prove2.me/submissions/5cda524f-6dab-4558-8b4c-5e2ccb9cd6c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn

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
theorem _root_.solution {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (hf : DifferentiableOn ℂ f (rectClosed z w)) : rectInt f z w = 0 := by
  have e : rectClosed z w = uIcc z.re w.re ×ℂ uIcc z.im w.im := by
    rw [rectClosed, uIcc_of_le hre, uIcc_of_le him]
  rw [e] at hf
  unfold rectInt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
end PI.EF.Rect
