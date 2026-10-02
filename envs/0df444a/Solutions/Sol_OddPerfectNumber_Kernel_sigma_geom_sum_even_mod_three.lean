-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_geom_sum_even_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:49:46.482855+00:00
-- url     : https://prove2.me/submissions/ae8d7ade-fe1c-42ca-87d5-43b500c25c00

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open scoped BigOperators

lemma sum_pow_two_mul (t : ℕ) (ht : t % 3 = 2) (m : ℕ) :
    (∑ i ∈ Finset.range (2 * m), t ^ i) % 3 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_split : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h_split, Finset.sum_range_succ, Finset.sum_range_succ]
    have h_pair : t ^ (2 * m) + t ^ (2 * m + 1) = t ^ (2 * m) * (1 + t) := by
      rw [pow_succ]
      ring
    have h_assoc : (∑ i ∈ Finset.range (2 * m), t ^ i) + t ^ (2 * m) + t ^ (2 * m + 1) =
        (∑ i ∈ Finset.range (2 * m), t ^ i) + (t ^ (2 * m) + t ^ (2 * m + 1)) := by ring
    rw [h_assoc, h_pair, Nat.add_mod, ih]
    have h1t : (1 + t) % 3 = 0 := by omega
    have h_term : (t ^ (2 * m) * (1 + t)) % 3 = 0 := by
      rw [Nat.mul_mod, h1t, mul_zero, Nat.zero_mod]
    rw [h_term]

theorem solution (t k : Nat) (ht : t % 3 = 2) (hk : k % 2 = 0) :
    (∑ i ∈ Finset.range k, t ^ i) % 3 = 0 := by
  have hk2 : k = 2 * (k / 2) := by omega
  rw [hk2]
  exact sum_pow_two_mul t ht (k / 2)
