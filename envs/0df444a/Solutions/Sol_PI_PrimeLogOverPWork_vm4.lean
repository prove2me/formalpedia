-- Prove2me | solution 1 for PI.PrimeLogOverPWork.vm4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:29.801529+00:00
-- url     : https://prove2.me/submissions/59f6af53-809d-4f1c-9e8a-cfc8cb40912d

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
theorem _root_.solution : Λ 4 = Real.log 2 := by
  rw [show (4:ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num
end PI.PrimeLogOverPWork
