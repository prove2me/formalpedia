-- Prove2me | solution 1 for PI.PrimeLogOverPWork.log_factorial_eq_sum_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:38.616808+00:00
-- url     : https://prove2.me/submissions/e709b4f6-0e72-4784-b233-6dc073e2059a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog

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
theorem _root_.solution (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    push_cast; ring
end PI.PrimeLogOverPWork
