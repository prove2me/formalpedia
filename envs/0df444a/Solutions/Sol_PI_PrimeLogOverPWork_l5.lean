-- Prove2me | solution 1 for PI.PrimeLogOverPWork.l5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:02.903596+00:00
-- url     : https://prove2.me/submissions/c9828abc-2206-471f-8b25-ec99f1eea27b

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
theorem _root_.solution : (46 : ℝ) / 20 * Real.log 2 ≤ Real.log (5 : ℝ) := by
  have h := le_log_of_pow_le 5 46 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith
end PI.PrimeLogOverPWork
