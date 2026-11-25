-- Prove2me | solution 1 for PI.EF.Rect.vint_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:33.416075+00:00
-- url     : https://prove2.me/submissions/e0b96b33-9f16-485c-89ad-e1f72b6519fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_continuousOn_vseg

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
theorem _root_.solution {F f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (h : ∀ y ∈ uIcc b₁ b₂, HasDerivAt F (f (a + y * I)) (a + y * I))
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    I • ∫ y : ℝ in b₁..b₂, f (a + y * I) = F (a + b₂ * I) - F (a + b₁ * I) := by
  have hd : ∀ y ∈ uIcc b₁ b₂, HasDerivAt (fun t : ℝ => F (a + t * I)) (f (a + y * I) * I) y := by
    intro y hy
    have hg : HasDerivAt (fun t : ℝ => (a : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (a : ℂ)
    exact (h y hy).comp y hg
  rw [← intervalIntegral.integral_smul]
  have e : (fun y : ℝ => I • f (a + y * I)) = fun y : ℝ => f (a + y * I) * I := by
    funext y
    rw [smul_eq_mul, mul_comm]
  rw [e]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_vseg hc).mul continuousOn_const).intervalIntegrable
end PI.EF.Rect
