-- Prove2me | solution 1 for PI.TailWork.sum_log_div_sq_le_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:59.566727+00:00
-- url     : https://prove2.me/submissions/e98d4985-6dd8-4d11-9175-5b937d7fd3bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogDivSqLeDiv
import Theorems.Thm_PI_TailWork_log_three_le
import Theorems.Thm_PI_TailWork_log_five_le
import Theorems.Thm_PI_TailWork_small_split
import Theorems.Thm_PI_TailWork_tail_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.TailWork
open Finset
private theorem sum_small_primes_log_div_sq_add_le (a : ℕ) (ha : a < 5) :
    ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
      + 2.04 / 7 ≤ 2.04 / ((a : ℝ) + 1) := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  interval_cases a <;> norm_num [Finset.sum_filter, Finset.sum_insert] <;> linarith
end PI.TailWork
end

set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (X : ℝ) (hX : 0 < X) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, ⌊X⌋₊ = m := ⟨_, rfl⟩
  have hXm : X < (m : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one X
  have hmX : (m : ℝ) ≤ X := hm ▸ Nat.floor_le hX.le
  have hlt : ∀ p ∈ Q, m < p := fun p hp => hm ▸ (Nat.floor_lt hX.le).2 (hQ p hp).2
  rcases lt_or_ge X 5 with h5 | h5
  · have hm5 : m < 5 := by exact_mod_cast (lt_of_le_of_lt hmX h5)
    have h1 := small_split m Q (fun p hp => ⟨(hQ p hp).1, hlt p hp⟩)
    have h2 := sum_small_primes_log_div_sq_add_le m hm5
    have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hXm.le
    have h3 : 2.04 / ((m : ℝ) + 1) ≤ 2.04 / X := by
      calc 2.04 / ((m : ℝ) + 1) = 2.04 * (1 / ((m : ℝ) + 1)) := by ring
        _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2.04 / X := by ring
    linarith
  · have hm5 : 5 ≤ m := by
      rw [← hm]; exact Nat.le_floor (by exact_mod_cast h5)
    obtain ⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k := ⟨_, rfl⟩
    have hk3 : 3 ≤ k := by omega
    have hQk : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p := by
      intro p hp
      have hpr := (hQ p hp).1
      have hmp := hlt p hp
      refine ⟨hpr, ?_⟩
      rcases hpr.eq_two_or_odd with h | h
      · omega
      · omega
    have h := tail_odd k hk3 Q hQk
    have hkX : X ≤ 2 * (k : ℝ) + 1 := by
      have hn : m + 1 ≤ 2 * k + 1 := by omega
      have : (m : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hn
      linarith
    have hinv : 1 / (2 * (k : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hkX
    calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := h
      _ = 2.04 * (1 / (2 * (k : ℝ) + 1)) := by ring
      _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2.04 / X := by ring
end PI.TailWork
