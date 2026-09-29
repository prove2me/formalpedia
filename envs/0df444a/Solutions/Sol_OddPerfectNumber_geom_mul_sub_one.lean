-- Prove2me | solution 1 for OddPerfectNumber.geom_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:14:51.922992+00:00
-- url     : https://prove2.me/submissions/d3d0c00d-84de-40c4-b98a-8058f07dd700

import Mathlib

-- STAGED direct proof, verbatim from the accepted DHP toolkit
-- (solution 7809bdb2), republished standalone.
theorem solution (p n : Nat) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range n, p ^ i) * (p - 1) = p ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
    have h2 : p ^ n ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp (by omega)
    have : p ^ n * (p - 1) = p ^ (n + 1) - p ^ n := by
      rw [Nat.mul_sub, mul_one, pow_succ]
    omega
