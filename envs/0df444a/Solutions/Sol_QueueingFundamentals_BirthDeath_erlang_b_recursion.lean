-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.erlang_b_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:25:00.875404+00:00
-- url     : https://prove2.me/submissions/09e4d63e-0256-432d-b75c-f72e2f465077

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

set_option autoImplicit false

open QueueingFundamentals.BirthDeath in
theorem erlangB_rec_aux (r : ℝ) (hr : 0 < r) (n : ℕ) :
    erlangB (n + 1) r = r * erlangB n r / (((n + 1 : ℕ) : ℝ) + r * erlangB n r) := by
  unfold erlangB
  set S : ℝ := ∑ i ∈ Finset.range (n + 1), r ^ i / (i.factorial : ℝ) with hS
  have hSpos : 0 < S := by
    rw [hS, Finset.sum_range_succ']
    have : 0 ≤ ∑ i ∈ Finset.range n, r ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    linarith
  rw [Finset.sum_range_succ, ← hS]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have ha : 0 < r ^ n := by positivity
  field_simp

open QueueingFundamentals.BirthDeath in
theorem solution (r : ℝ) (hr : 0 < r) :
    erlangB 0 r = 1 ∧
      ∀ c : ℕ, 1 ≤ c →
        erlangB c r = r * erlangB (c - 1) r / ((c : ℝ) + r * erlangB (c - 1) r) := by
  refine ⟨?_, ?_⟩
  · simp [erlangB]
  · intro c hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    simpa using erlangB_rec_aux r hr n
