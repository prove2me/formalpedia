-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_2_2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:58.01519+00:00
-- url     : https://prove2.me/submissions/8c496d2c-c1b0-4d6d-9150-058dbc92e616

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_S_2

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
theorem _root_.solution : S 2 ≤ Real.log (2 : ℝ) := by
  rw [S_2]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith
end PI.PrimeLogOverPWork
