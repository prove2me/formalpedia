-- Prove2me | solution 1 for PI.EF.Rect.continuousOn_vseg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:44.598546+00:00
-- url     : https://prove2.me/submissions/5222ecb4-c781-425c-a28e-1438b09d8a8b

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
theorem _root_.solution {f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc b₁ b₂) := by
  intro y hy
  exact (ContinuousAt.comp (f := fun t : ℝ => (a : ℂ) + t * I) (x := y) (hc y hy)
    (by fun_prop)).continuousWithinAt
end PI.EF.Rect
