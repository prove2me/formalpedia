-- Prove2me | solution 1 for PI.PrimeLogOverPWork.log_factorial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:03.738076+00:00
-- url     : https://prove2.me/submissions/9ac727c0-9508-4e75-99e2-e482288fe4ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_eq_sum_log

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
    Real.log (n ! : ℝ) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∀ k ∈ Ioc 0 n, Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d :=
    fun k _ => vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1,
    Finset.sum_comm' (t' := Ioc 0 n) (s' := fun d => (Ioc 0 n).filter (fun k => d ∣ k))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro k d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk0, hkn⟩, hdk, -⟩
      exact ⟨⟨⟨hk0, hkn⟩, hdk⟩, Nat.pos_of_dvd_of_pos hdk hk0, (Nat.le_of_dvd hk0 hdk).trans hkn⟩
    · rintro ⟨⟨⟨hk0, hkn⟩, hdk⟩, -⟩
      exact ⟨⟨hk0, hkn⟩, hdk, hk0.ne'⟩
end PI.PrimeLogOverPWork
