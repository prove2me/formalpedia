-- Prove2me | solution 1 for PI.TailWork.sum_log_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:32.336947+00:00
-- url     : https://prove2.me/submissions/7a5b98e5-dacc-498c-8473-3e2680e31071

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (n : ℕ) :
    ∑ p ∈ (Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  classical
  have hdvd : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ∣ Nat.centralBinom n := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.prime
    · intro p hp
      obtain ⟨hI, hpr⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hI
      rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
      exact hpr.dvd_choose_add h1 h1 (by omega)
  have hle : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ≤ 4 ^ n :=
    (Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd).trans (Nat.centralBinom_le_four_pow n)
  have hpos : ∀ p ∈ (Ioc n (2 * n)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [← Real.log_prod hpos, ← Real.log_pow]
  apply Real.log_le_log
  · apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.pos
  · have : ((∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at this
    exact this
end PI.TailWork
