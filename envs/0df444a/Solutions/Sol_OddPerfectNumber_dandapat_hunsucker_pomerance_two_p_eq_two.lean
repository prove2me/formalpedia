-- Prove2me | solution 1 for OddPerfectNumber.dandapat_hunsucker_pomerance_two_p_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:01:30.648481+00:00
-- url     : https://prove2.me/submissions/5a13f361-ffa4-42c9-a946-f84f4bbcb621

import Mathlib

theorem solution (p k m : Nat)
    (hp : p.Prime) (hm : Odd m) (hk : k ≠ 0) (hp2 : p = 2)
    (h1 : (∑ d ∈ (p ^ k).divisors, d) = 2 * m ^ 2)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ k) : False := by
  subst hp2
  have hp2prime : Nat.Prime 2 := by norm_num
  -- `σ(2^k)` is a sum of one odd term and `k` even terms, hence odd.
  have hodd : ∀ k, Odd (∑ i ∈ Finset.range (k + 1), 2 ^ i) := by
    intro k
    induction k with
    | zero => decide
    | succ n ih =>
      rw [Finset.sum_range_succ]
      apply Odd.add_even ih
      exact ⟨2 ^ n, by ring⟩
  have hoddσ : Odd (∑ d ∈ ((2 : ℕ) ^ k).divisors, d) := by
    rw [Nat.sum_divisors_prime_pow hp2prime]
    exact hodd k
  -- But it equals the visibly even number `2 * m^2`.
  rw [h1] at hoddσ
  have heven : Even (2 * m ^ 2) := even_two_mul (m ^ 2)
  exact (Nat.not_even_iff_odd.mpr hoddσ) heven
