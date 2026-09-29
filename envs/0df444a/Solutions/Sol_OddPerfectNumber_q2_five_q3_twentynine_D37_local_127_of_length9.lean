-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D37_local_127_of_length9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:18:53.05788+00:00
-- url     : https://prove2.me/submissions/78999195-bb28-4e0a-a74a-cec1a819ec66

import Mathlib

theorem solution (n k : Nat)
    (hlen : n = 9 * k) :
    127 ∣ ∑ i ∈ Finset.range n, 37 ^ i := by
  subst n
  have hblock : 127 ∣ ∑ i ∈ Finset.range 9, 37 ^ i := by
    norm_num [Finset.sum_range_succ]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have hshift :
          (∑ x ∈ Finset.range 9, 37 ^ (9 * k + x)) =
            37 ^ (9 * k) * (∑ x ∈ Finset.range 9, 37 ^ x) := by
        simp [pow_add, Finset.mul_sum, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [hshift]
      exact dvd_add ih (dvd_mul_of_dvd_right hblock _)
