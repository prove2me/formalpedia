-- Prove2me | solution 1 for PI.PrimeLogOverPWork.log_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:06.314846+00:00
-- url     : https://prove2.me/submissions/8b5d4f6d-275c-47e9-abd5-73713b8cecd9

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
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n ! : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hlog := Real.log_le_log (Stirling.stirlingSeq'_pos k) hanti
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num), Real.log_div hpos.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num) hpos.ne'] at hlog
  push_cast at hlog ⊢
  linarith
end PI.PrimeLogOverPWork
