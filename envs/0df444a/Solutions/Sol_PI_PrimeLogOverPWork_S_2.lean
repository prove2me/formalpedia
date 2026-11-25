-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:06.014071+00:00
-- url     : https://prove2.me/submissions/8f6fe74b-8624-43a1-822d-4351ea3bc634

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
theorem _root_.solution : S 2 = Real.log 2 / 2 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']
end PI.PrimeLogOverPWork
