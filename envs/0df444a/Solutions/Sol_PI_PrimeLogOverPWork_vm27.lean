-- Prove2me | solution 1 for PI.PrimeLogOverPWork.vm27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:24.171798+00:00
-- url     : https://prove2.me/submissions/c01dea6d-732e-4670-a12f-aa7a56ede704

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
theorem _root_.solution : Λ 27 = Real.log 3 := by
  rw [show (27:ℕ) = 3 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_three]
  norm_num
end PI.PrimeLogOverPWork
