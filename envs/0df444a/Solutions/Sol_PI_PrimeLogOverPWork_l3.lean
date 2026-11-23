-- Prove2me | solution 1 for PI.PrimeLogOverPWork.l3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:46.050831+00:00
-- url     : https://prove2.me/submissions/b2b31374-1e62-4595-bf25-433808bed29e

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
theorem _root_.solution : (31 : ℝ) / 20 * Real.log 2 ≤ Real.log (3 : ℝ) := by
  have h := le_log_of_pow_le 3 31 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith
end PI.PrimeLogOverPWork
