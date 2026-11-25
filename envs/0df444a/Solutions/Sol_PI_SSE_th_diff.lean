-- Prove2me | solution 1 for PI.SSE.th_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:43.883751+00:00
-- url     : https://prove2.me/submissions/9d42e396-d2e9-4913-a02d-327e16c70284

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (τ : ℂ) (hτ : 0 < τ.im) : Differentiable ℂ (th τ) := by
  intro u
  unfold th
  exact (((differentiableAt_id.const_mul (↑Real.pi * I)).cexp)).mul
    ((differentiableAt_jacobiTheta₂_fst (u + (1 / 2 + τ / 2)) hτ).comp u (differentiableAt_id.add_const _))
end PI.SSE
