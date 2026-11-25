-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_3_4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:44.743629+00:00
-- url     : https://prove2.me/submissions/29fbb725-1006-4a04-bb57-05034e3b4fe5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_l3
import Theorems.Thm_PI_PrimeLogOverPWork_S_4

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
theorem _root_.solution : S 4 ≤ Real.log (3 : ℝ) := by
  rw [S_4]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l3
  linarith
end PI.PrimeLogOverPWork
