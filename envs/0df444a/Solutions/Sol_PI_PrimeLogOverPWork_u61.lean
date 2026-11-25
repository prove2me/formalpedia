-- Prove2me | solution 1 for PI.PrimeLogOverPWork.u61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:23.655796+00:00
-- url     : https://prove2.me/submissions/505fe15f-a72c-4c97-8100-c2256272839e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Theorems.Thm_PI_PrimeLogOverPWork_log_le_of_pow_le


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
theorem _root_.solution : Real.log (61 : ℝ) ≤ 119 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 61 119 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith
end PI.PrimeLogOverPWork
