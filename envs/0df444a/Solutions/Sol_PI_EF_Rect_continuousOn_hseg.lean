-- Prove2me | solution 1 for PI.EF.Rect.continuousOn_hseg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:39.585144+00:00
-- url     : https://prove2.me/submissions/9de62d34-3959-4483-957b-b5e4459632bb

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
theorem _root_.solution {f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ContinuousOn (fun x : ℝ => f (x + b * I)) (uIcc a₁ a₂) := by
  intro x hx
  exact (ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + b * I) (x := x) (hc x hx)
    (by fun_prop)).continuousWithinAt
end PI.EF.Rect
