-- Prove2me | solution 2 for SphereGRF.Spectral.factorial_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:45:00.323216+00:00
-- url     : https://prove2.me/submissions/3805c942-4b49-46a2-9204-089961d2f92e

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ, n ≤ ℓ →
      c₁ * (ℓ : ℝ) ^ (2 * n) ≤ ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ∧
      ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ≤ c₂ * (ℓ : ℝ) ^ (2 * n) := by
  refine ⟨1 / ((n : ℝ) ^ (2 * n)), 4 ^ n, ?_, by positivity, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : (0 : ℝ) < n := by exact_mod_cast h
      positivity
  intro ℓ hl
  have key : ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ)
      = (((ℓ + n).descFactorial (2 * n) : ℕ) : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (show 2 * n ≤ ℓ + n by omega)
    rw [show ℓ + n - 2 * n = ℓ - n by omega] at h
    have hpos : ((ℓ - n).factorial : ℝ) ≠ 0 := by positivity
    rw [div_eq_iff hpos]
    have h' : (((ℓ - n).factorial * (ℓ + n).descFactorial (2 * n) : ℕ) : ℝ) = (((ℓ + n).factorial : ℕ) : ℝ) := by
      rw [h]
    push_cast at h'
    rw [← h']; ring
  rw [key]
  constructor
  · rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn : (0 : ℝ) < n := by exact_mod_cast h
      have h1 : (((ℓ + n + 1 - 2 * n) ^ (2 * n) : ℕ) : ℝ) ≤ (((ℓ + n).descFactorial (2 * n) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_sub_le_descFactorial (ℓ + n) (2 * n)
      have e : ((ℓ + n + 1 - 2 * n : ℕ) : ℝ) = (ℓ : ℝ) - n + 1 := by
        rw [show ℓ + n + 1 - 2 * n = (ℓ - n) + 1 by omega, Nat.cast_add, Nat.cast_sub hl]; simp
      push_cast [e] at h1
      have h2 : (ℓ : ℝ) / n ≤ (ℓ : ℝ) - n + 1 := by
        rw [div_le_iff₀ hn]
        have h1' : (1 : ℝ) ≤ n := by exact_mod_cast h
        have : (n : ℝ) ≤ ℓ := by exact_mod_cast hl
        nlinarith
      have h3 : ((ℓ : ℝ) / n) ^ (2 * n) ≤ ((ℓ : ℝ) - n + 1) ^ (2 * n) :=
        pow_le_pow_left₀ (by positivity) h2 _
      calc 1 / ((n : ℝ) ^ (2 * n)) * (ℓ : ℝ) ^ (2 * n) = ((ℓ : ℝ) / n) ^ (2 * n) := by
            rw [div_pow]; ring
        _ ≤ _ := h3.trans h1
  · have h1 : (((ℓ + n).descFactorial (2 * n) : ℕ) : ℝ) ≤ (((ℓ + n) ^ (2 * n) : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_le_pow (ℓ + n) (2 * n)
    have h2 : ((ℓ : ℝ) + n) ≤ 2 * ℓ := by
      have : (n : ℝ) ≤ ℓ := by exact_mod_cast hl
      linarith
    have h3 : ((ℓ : ℝ) + n) ^ (2 * n) ≤ (2 * (ℓ : ℝ)) ^ (2 * n) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : (2 * (ℓ : ℝ)) ^ (2 * n) = 4 ^ n * (ℓ : ℝ) ^ (2 * n) := by
      rw [mul_pow, pow_mul]; norm_num
    push_cast at h1
    linarith
