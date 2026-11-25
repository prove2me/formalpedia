-- Prove2me | solution 1 for PI.PrimeLogOverPWork.vm25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:19.68299+00:00
-- url     : https://prove2.me/submissions/ee919db4-d2c4-4936-90ec-4f682b8ff2f0

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
theorem _root_.solution : Λ 25 = Real.log 5 := by
  rw [show (25:ℕ) = 5 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    vonMangoldt_apply_prime Nat.prime_five]
  norm_num
end PI.PrimeLogOverPWork
