-- Prove2me | solution 1 for PI.SSE.exp_int_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:04.316487+00:00
-- url     : https://prove2.me/submissions/6ae73591-a823-4ccd-963f-6d431084a26e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (k : ℤ) : cexp (k * (Real.pi * I)) = (-1 : ℂ) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
end PI.SSE
