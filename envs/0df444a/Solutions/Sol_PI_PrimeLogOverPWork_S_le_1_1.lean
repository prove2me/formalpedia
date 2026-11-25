-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_1_1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:37.962444+00:00
-- url     : https://prove2.me/submissions/f467dc74-2819-41fb-887b-9cc34c171dfc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_S_1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset
namespace PI.PrimeLogOverPWork
theorem _root_.solution : S 1 ≤ Real.log (1 : ℝ) := by
  rw [S_1, Real.log_one]
end PI.PrimeLogOverPWork
