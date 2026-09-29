-- Prove2me | solution 1 for OddPerfectNumber.no_dris_thirteen_s_ge_two_even
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:13:07.135033+00:00
-- url     : https://prove2.me/submissions/ba759c91-746e-4dab-a9ac-1dd5d667d7f9

import Mathlib

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hs2 : 2 ≤ s) (hs_even : Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  have h14 : (1 : ℕ) % 4 = 1 := by decide
  have hterm : ∀ i : ℕ, p ^ i % 4 = 1 := by
    intro i
    have h := Nat.pow_mod p i 4
    rw [hp4, one_pow] at h
    have h2 : p ^ i % 4 = 1 % 4 := h
    rw [h14] at h2
    exact h2
  -- Since `k ≡ 1 mod 4`, the `k+1` summands each contribute `1 mod 4`,
  -- so `σ(p^k) ≡ k+1 ≡ 2 mod 4`; `omega` closes with `hk4` in context.
  have hσ : (∑ d ∈ (p ^ k).divisors, d) % 4 = 2 := by
    simp only [Nat.sum_divisors_prime_pow hp]
    rw [Finset.sum_nat_mod]
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_range]
    simp only [smul_eq_mul, mul_one]
    omega
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by
    obtain ⟨j, hj⟩ := hm
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
    obtain ⟨j, hj⟩ := hs_even
    omega
  intro hcon
  obtain ⟨h1, h2⟩ := hcon
  -- NB: rewrite the goal forward; `rw` auto-closes definitional goals, so
  -- no trailing tactic may follow (a dead `decide` errors with no goals).
  have e1 : (2 * m ^ 2) % 4 = 2 := by
    rw [Nat.mul_mod, hm2]
  have e2 : ((∑ d ∈ (p ^ k).divisors, d) * s) % 4 = 0 := by
    rw [Nat.mul_mod, hσ]
    rcases hs0 with h0 | h0 <;> rw [h0]
  rw [h1] at e1
  omega
