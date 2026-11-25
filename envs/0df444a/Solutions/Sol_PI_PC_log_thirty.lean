-- Prove2me | solution 1 for PI.PC.log_thirty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:12.21822+00:00
-- url     : https://prove2.me/submissions/69a2e85e-70a7-4db8-ace7-1c92b8fae59d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution : log 30 = log 2 + log 3 + log 5 := by
  rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
  norm_num
end PI.PC
