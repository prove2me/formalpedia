-- Prove2me | solution 1 for PI.PrimeLogOverPWork.log_factorial_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:36.169627+00:00
-- url     : https://prove2.me/submissions/9d19d0f5-71b3-4ee7-8cad-4113bf35b068

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Theorems.Thm_PI_PrimeLogOverPWork_sum_E_ge
import Theorems.Thm_PI_PrimeLogOverPWork_sum_primes_ge
import Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_eq


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
theorem _root_.solution (n : ℕ) (hn : 27 ≤ n) :
    (n : ℝ) * S n - Chebyshev.theta n
      + (Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1)) ≤ Real.log (n ! : ℝ) := by
  rw [log_factorial_eq]
  have hdisj : Disjoint ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) E := by
    rw [Finset.disjoint_right]
    intro d hd
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hd
    simp only [Finset.mem_filter, not_and]
    intro _
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsub : ({d ∈ Ioc 0 n | d.Prime} : Finset ℕ) ∪ E ⊆ Ioc 0 n := by
    intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact (Finset.mem_filter.mp h).1
    · simp only [E, Finset.mem_insert, Finset.mem_singleton] at h
      rw [Finset.mem_Ioc]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun d => Λ d * ((n / d : ℕ) : ℝ))
    (fun d _ _ => mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  rw [Finset.sum_union hdisj] at hle
  have h1 := sum_primes_ge n
  have h2 := sum_E_ge n
  linarith
end PI.PrimeLogOverPWork
