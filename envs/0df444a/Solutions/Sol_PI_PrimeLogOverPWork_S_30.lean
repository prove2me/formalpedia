-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:10.534662+00:00
-- url     : https://prove2.me/submissions/1dc844bf-3de0-4fb6-8988-95b9812f97e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.PrimeLogOverPWork
open Finset
private theorem S_zero' : S 0 = 0 := by
  simp [S]
private theorem S_succ_eq_add_ite_prime (n : ℕ) :
    S (n + 1) = S n +
      if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
  simp only [S, Finset.sum_filter]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
end PI.PrimeLogOverPWork
end

set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset
namespace PI.PrimeLogOverPWork
theorem _root_.solution : S 30 = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 + Real.log 7 / 7 + Real.log 11 / 11 + Real.log 13 / 13 + Real.log 17 / 17 + Real.log 19 / 19 + Real.log 23 / 23 + Real.log 29 / 29 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']
end PI.PrimeLogOverPWork
