-- Prove2me | solution 1 for PI.PrimeLogOverPWork.l11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:31.77171+00:00
-- url     : https://prove2.me/submissions/9a537ef5-d4e0-43c2-a5e6-2f51de454349

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_le_log_of_pow_le


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
theorem _root_.solution : (69 : ℝ) / 20 * Real.log 2 ≤ Real.log (11 : ℝ) := by
  have h := le_log_of_pow_le 11 69 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith
end PI.PrimeLogOverPWork
