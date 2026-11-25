-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:25.232037+00:00
-- url     : https://prove2.me/submissions/ccff2ea8-5db6-4e28-a305-6b0b5c1fbcd8

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : S m ≤ S n := by
  unfold S
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans h⟩, hx.2⟩
  · intro x hx _
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast hx.1.1
end PI.PrimeLogOverPWork
