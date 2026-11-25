-- Prove2me | solution 1 for PI.PrimeLogOverPWork.vm8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:36.32419+00:00
-- url     : https://prove2.me/submissions/cf6e2e23-27f6-4117-baa2-d5561d4c3207

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution : Λ 8 = Real.log 2 := by
  rw [show (8:ℕ) = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num
end PI.PrimeLogOverPWork
