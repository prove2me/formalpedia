-- Prove2me | solution 1 for QuantumLTF.Membership.ceil_logb_bits_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:18:07.567232+00:00
-- url     : https://prove2.me/submissions/7e438460-503c-4847-8026-f5db46ae711d

import Mathlib

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ((4 + ⌈Real.logb 2 n⌉₊ : ℕ) : ℝ) ≤ C * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨6 / Real.log 2, by positivity, ?_⟩
  intro n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have hb : Real.logb 2 n = Real.log n / Real.log 2 := rfl
  have hb1 : 1 ≤ Real.logb 2 n := by
    rw [hb, le_div_iff₀ hl2]; linarith
  have hceil : (⌈Real.logb 2 n⌉₊ : ℝ) < Real.logb 2 n + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  push_cast
  have : 6 / Real.log 2 * Real.log n = 6 * Real.logb 2 n := by
    rw [hb]; field_simp
  rw [this]
  linarith
