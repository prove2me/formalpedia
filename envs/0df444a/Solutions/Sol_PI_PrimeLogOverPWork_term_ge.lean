-- Prove2me | solution 1 for PI.PrimeLogOverPWork.term_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:01.594229+00:00
-- url     : https://prove2.me/submissions/f7470099-ad53-4e18-bb00-cfe00b6ac2da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Theorems.Thm_PI_PrimeLogOverPWork_div_sub_one_le


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
theorem _root_.solution (n d : ℕ) : Λ d * ((n : ℝ) / d - 1) ≤ Λ d * ((n / d : ℕ) : ℝ) :=
  mul_le_mul_of_nonneg_left (div_sub_one_le n d) vonMangoldt_nonneg
end PI.PrimeLogOverPWork
