-- Prove2me | solution 1 for PI.PrimeLogOverPWork.sum_primes_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:09.110991+00:00
-- url     : https://prove2.me/submissions/237c6328-3892-4f3f-8672-73bf18f7a0e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Theorems.Thm_PI_PrimeLogOverPWork_term_ge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
private theorem theta_eq_sum_log_primes (n : ℕ) :
    Chebyshev.theta n = ∑ p ∈ Ioc 0 n with p.Prime, Real.log p := by
  simp [Chebyshev.theta]
end PI.PrimeLogOverPWork
end

set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution (n : ℕ) :
    (n : ℝ) * S n - Chebyshev.theta n
      ≤ ∑ d ∈ Ioc 0 n with d.Prime, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [theta_eq_sum_log_primes, S, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have h := term_ge n p
  rw [vonMangoldt_apply_prime hpp] at h ⊢
  calc (n : ℝ) * (Real.log p / p) - Real.log p = Real.log p * ((n : ℝ) / p - 1) := by ring
    _ ≤ _ := h
end PI.PrimeLogOverPWork
