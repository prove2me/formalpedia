-- Prove2me | solution 1 for PI.PrimeLogOverPWork.l31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:34.635391+00:00
-- url     : https://prove2.me/submissions/f3d620a3-c317-486f-b3e0-2ff6e2cb0921

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
theorem _root_.solution : (99 : ℝ) / 20 * Real.log 2 ≤ Real.log (31 : ℝ) := by
  have h := le_log_of_pow_le 31 99 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith
end PI.PrimeLogOverPWork
