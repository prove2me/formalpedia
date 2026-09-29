-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:38:56.362011+00:00
-- url     : https://prove2.me/submissions/fac96f29-c57f-4a06-88a0-59c0db593dec

import Mathlib

theorem solution (p : Nat) (hp : 2 < p) :
    (¬ ∃ a, a ^ 2 = p ^ 2 + p + 1) ∧ (¬ ∃ b, b ^ 2 = p ^ 2 - p + 1) := by
  have key : ∀ q : ℕ, 1 ≤ q → ¬ ∃ a, a ^ 2 = q ^ 2 + q + 1 := by
    rintro q hq ⟨a, ha⟩
    have e : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    rcases Nat.lt_or_ge q a with h | h
    · have : (q + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h 2
      omega
    · have : a ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h 2
      omega
  refine ⟨key p (by omega), ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  have h' : (q + 1) ^ 2 - (q + 1) + 1 = q ^ 2 + q + 1 := by omega
  rw [h']
  exact key q (by omega)
