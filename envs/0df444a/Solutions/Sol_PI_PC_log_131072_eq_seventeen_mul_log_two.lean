-- Prove2me | solution 1 for PI.PC.log_131072_eq_seventeen_mul_log_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:07.054179+00:00
-- url     : https://prove2.me/submissions/cbb514aa-4b02-46b6-a968-9049d7997ef1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution : log 131072 = 17 * log 2 := by
  rw [show (131072 : ℝ) = 2 ^ 17 by norm_num, Real.log_pow]; norm_num
end PI.PC
