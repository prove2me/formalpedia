-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_geom_sum_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:44:03.46199+00:00
-- url     : https://prove2.me/submissions/e0ee7ae9-c999-4109-a122-1a1159947ddd

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open scoped BigOperators

lemma pow_mod_three (t : ℕ) (ht : t % 3 = 1) (n : ℕ) : (t ^ n) % 3 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih, ht]

lemma sum_pow_mod_three (t : ℕ) (ht : t % 3 = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, t ^ i) % 3 = n % 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, pow_mod_three t ht]
    omega

theorem solution (t e : Nat) (ht : t % 3 = 1) :
    (∑ i ∈ Finset.range (2 * e + 1), t ^ i) % 3 = (2 * e + 1) % 3 :=
  sum_pow_mod_three t ht (2 * e + 1)
