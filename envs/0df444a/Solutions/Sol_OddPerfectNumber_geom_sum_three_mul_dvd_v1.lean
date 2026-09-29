-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_three_mul_dvd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:47:46.159326+00:00
-- url     : https://prove2.me/submissions/d7df9b6f-1b78-4a3c-aaa0-f03f3a388b46

import Mathlib

theorem solution (q k : Nat) :
    (∑ i ∈ Finset.range 3, q ^ i) ∣ (∑ i ∈ Finset.range (3 * k), q ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : 3 * (k + 1) = 3 * k + 3 := by ring
    rw [hsplit, Finset.sum_range_add]
    apply dvd_add ih
    have hfactor : (∑ i ∈ Finset.range 3, q ^ (3 * k + i))
        = q ^ (3 * k) * (∑ i ∈ Finset.range 3, q ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
    rw [hfactor]
    exact dvd_mul_left _ _
