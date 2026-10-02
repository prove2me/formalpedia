-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_geom_sum_mod_three_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:50:23.661277+00:00
-- url     : https://prove2.me/submissions/04d7b955-5b88-4a42-b107-f58787217df4

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open scoped BigOperators

lemma geom_sum_pair_mod_three (t : ℕ) (ht : t % 3 = 0 ∨ t % 3 = 2) (e : ℕ) :
    (t ^ (2 * e + 1) + t ^ (2 * e + 2)) % 3 = 0 := by
  rcases ht with ht0 | ht2
  · have h_factor : t ^ (2 * e + 1) + t ^ (2 * e + 2) = (t ^ (2 * e) + t ^ (2 * e + 1)) * t := by
      rw [pow_succ, pow_succ]
      ring
    rw [h_factor, Nat.mul_mod, ht0, mul_zero, Nat.zero_mod]
  · have h_pair : t ^ (2 * e + 1) + t ^ (2 * e + 2) = t ^ (2 * e + 1) * (1 + t) := by
      rw [pow_succ]
      ring
    rw [h_pair, Nat.mul_mod]
    have h1t : (1 + t) % 3 = 0 := by omega
    rw [h1t, mul_zero, Nat.zero_mod]

lemma sum_pow_odd_step (t : ℕ) (ht : t % 3 = 0 ∨ t % 3 = 2) (e : ℕ) :
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 3 = 1 := by
  induction e with
  | zero =>
    rw [Finset.sum_range_one, pow_zero]
    omega
  | succ e ih =>
    have h_split : 2 * (e + 1) + 1 = 2 * e + 1 + 1 + 1 := by omega
    rw [h_split, Finset.sum_range_succ, Finset.sum_range_succ]
    have h_assoc : (∑ i ∈ Finset.range (2 * e + 1), t ^ i) + t ^ (2 * e + 1) + t ^ (2 * e + 2) =
        (∑ i ∈ Finset.range (2 * e + 1), t ^ i) + (t ^ (2 * e + 1) + t ^ (2 * e + 2)) := by ring
    rw [h_assoc, Nat.add_mod, ih, geom_sum_pair_mod_three t ht e]
    try omega

theorem solution (t e : Nat) (ht : t % 3 != 1) :
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 3 = 1 := by
  have ht_or : t % 3 = 0 ∨ t % 3 = 2 := by
    have h_ne : t % 3 ≠ 1 := by
      intro h_eq
      rw [h_eq] at ht
      revert ht
      decide
    omega
  exact sum_pow_odd_step t ht_or e
