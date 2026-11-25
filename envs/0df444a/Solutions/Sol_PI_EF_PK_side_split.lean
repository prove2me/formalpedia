-- Prove2me | solution 1 for PI.EF.PK.side_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:02.868313+00:00
-- url     : https://prove2.me/submissions/fc6fed42-104c-40eb-91a9-bfa1d9686cf1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_gl_differentiable
import Theorems.Thm_PI_EF_PK_ker_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l : ℝ) (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : ∀ t, γ t ≠ 0) (p q : ℝ) :
    ∫ t in p..q, ker l (γ t) = (∫ t in p..q, gl l (γ t)) + ∫ t in p..q, 1 / (γ t - 0) := by
  have hpt : ∀ t, ker l (γ t) = gl l (γ t) + 1 / (γ t - 0) := fun t => ker_eq l (h0 t)
  simp_rw [hpt]
  apply intervalIntegral.integral_add
  · apply Continuous.intervalIntegrable
    exact (gl_differentiable l).continuous.comp hγ
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (hγ.sub continuous_const) (fun t => by simpa using h0 t)
end PI.EF.PK
