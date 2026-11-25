-- Prove2me | solution 1 for PI.SSE.thetaA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:53.717842+00:00
-- url     : https://prove2.me/submissions/a998367d-37d9-46df-98c9-bbad2b22ab0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA
import Theorems.Thm_PI_SSE_th_add_one
import Theorems.Thm_PI_SSE_th_add_tau
import Theorems.Thm_PI_SSE_th_neg
import Theorems.Thm_PI_SSE_th_diff
import Theorems.Thm_PI_SSE_th_deriv

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
theorem _root_.solution : ThetaA := by
  intro τ hτ
  exact ⟨th_diff τ hτ, th_neg τ, th_add_one τ, th_add_tau τ, th_deriv τ hτ⟩
end PI.SSE
