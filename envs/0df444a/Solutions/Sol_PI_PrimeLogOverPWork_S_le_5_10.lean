-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_5_10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:08.306427+00:00
-- url     : https://prove2.me/submissions/36cbe4f9-03c8-4180-bbe4-c07ca618421d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_u3
import Theorems.Thm_PI_PrimeLogOverPWork_u7
import Theorems.Thm_PI_PrimeLogOverPWork_l5
import Theorems.Thm_PI_PrimeLogOverPWork_S_10

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
theorem _root_.solution : S 10 ≤ Real.log (5 : ℝ) := by
  rw [S_10]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l5
  have hb0 := u3
  have hb1 := u7
  linarith
end PI.PrimeLogOverPWork
