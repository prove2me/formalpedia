-- Prove2me | solution 1 for PI.EF.Rect.rectInt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:42.764173+00:00
-- url     : https://prove2.me/submissions/3441f3d4-1cb5-48db-9ce0-c727422f1f67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_sides_integrable

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
theorem _root_.solution {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w))
    (hg : ContinuousOn g (rectBdry z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  obtain ⟨f1, f2, f3, f4⟩ := sides_integrable hf
  obtain ⟨g1, g2, g3, g4⟩ := sides_integrable hg
  unfold rectInt
  beta_reduce
  rw [intervalIntegral.integral_add f1 g1, intervalIntegral.integral_add f2 g2,
    intervalIntegral.integral_add f3 g3, intervalIntegral.integral_add f4 g4]
  simp only [smul_eq_mul]
  ring
end PI.EF.Rect
