-- Prove2me | solution 1 for PI.EF.Rect.hint_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:49.157577+00:00
-- url     : https://prove2.me/submissions/c6cec9f3-771b-424f-870b-3ccee0810a84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_continuousOn_hseg

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
theorem _root_.solution {F f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (h : ∀ x ∈ uIcc a₁ a₂, HasDerivAt F (f (x + b * I)) (x + b * I))
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ∫ x : ℝ in a₁..a₂, f (x + b * I) = F (a₂ + b * I) - F (a₁ + b * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + b * I))
    (fun x hx => ?_) (continuousOn_hseg hc).intervalIntegrable
  have hg : HasDerivAt (fun t : ℝ => (t : ℂ) + b * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((b : ℂ) * I)
  have hd := (h x hx).comp x hg
  rw [mul_one] at hd
  exact hd
end PI.EF.Rect
