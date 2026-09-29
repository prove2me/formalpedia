-- Prove2me | solution 1 for OddPerfectNumber.no_dris_five_s_ge_two_even
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T23:20:08.50979+00:00
-- url     : https://prove2.me/submissions/fd690420-cd17-4620-a637-0b69bf744c1f

import Mathlib

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) (hs_even : Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  have h14 : (1 : ℕ) % 4 = 1 := by decide
  have hterm : ∀ i : ℕ, p ^ i % 4 = 1 := by
    intro i
    have h := Nat.pow_mod p i 4
    rw [hp4, one_pow] at h
    have h2 : p ^ i % 4 = 1 % 4 := h
    rw [h14] at h2
    exact h2
  have hσ : (∑ d ∈ (p ^ 5).divisors, d) % 4 = 2 := by
    -- NB: `Finset.sum_nat_mod` must go through `rw`: under `simp` its
    -- right-hand side re-matches and Lean hits max recursion depth.
    simp only [Nat.sum_divisors_prime_pow hp]
    rw [Finset.sum_nat_mod]
    simp only [hterm]
    decide
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hm2 : m ^ 2 % 4 = 1 := by
    have h := Nat.pow_mod m 2 4
    rcases hm4 with h4 | h4 <;> rw [h4] at h
    · have hq : (1 : ℕ) ^ 2 % 4 = 1 := by decide
      rw [hq] at h
      exact h
    · have hq : (3 : ℕ) ^ 2 % 4 = 1 := by decide
      rw [hq] at h
      exact h
  have hs0 : s % 4 = 0 ∨ s % 4 = 2 := by
    obtain ⟨k, hk⟩ := hs_even
    omega
  intro hcon
  obtain ⟨h1, h2⟩ := hcon
  -- NB: rewrite the goal forward; `rw` auto-closes definitional goals, so
  -- no trailing tactic may follow (a dead `decide` errors with no goals).
  -- Hand-restated `*`/`%` shapes must also be avoided (prior mismatch).
  have e1 : (2 * m ^ 2) % 4 = 2 := by
    rw [Nat.mul_mod, hm2]
  have e2 : ((∑ d ∈ (p ^ 5).divisors, d) * s) % 4 = 0 := by
    rw [Nat.mul_mod, hσ]
    rcases hs0 with h0 | h0 <;> rw [h0]
  rw [h1] at e1
  omega
