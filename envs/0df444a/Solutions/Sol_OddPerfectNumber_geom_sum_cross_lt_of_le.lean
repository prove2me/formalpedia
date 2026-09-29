-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_cross_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T12:16:21.594583+00:00
-- url     : https://prove2.me/submissions/48db25b6-53f2-4ffc-a55c-5322c6d77254

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_power_sigma_euler_upper_bound

theorem solution (r q a : Nat)
    (hr : 2 ≤ r) (hrq : r ≤ q) (hq : q.Prime) :
    (r - 1) * (∑ i ∈ Finset.range (a + 1), q ^ i) <
      r * q ^ a := by
  let S : Nat := ∑ i ∈ Finset.range (a + 1), q ^ i
  have hqone : 1 < q := lt_of_lt_of_le (by omega) hrq
  have hupper : (q - 1) * S < q ^ (a + 1) := by
    dsimp [S]
    exact OddPerfectNumber.prime_power_sigma_euler_upper_bound q a hqone
  have hcoef : q * (r - 1) ≤ r * (q - 1) := by
    calc
      q * (r - 1) = q * r - q := by
        rw [Nat.mul_sub_left_distrib]
        simp
      _ ≤ q * r - r := Nat.sub_le_sub_left hrq (q * r)
      _ = r * q - r := by rw [Nat.mul_comm q r]
      _ = r * (q - 1) := by
        rw [Nat.mul_sub_left_distrib]
        simp
  have hmul : q * ((r - 1) * S) ≤ r * ((q - 1) * S) := by
    calc
      q * ((r - 1) * S) = (q * (r - 1)) * S := by ring
      _ ≤ (r * (q - 1)) * S := Nat.mul_le_mul_right S hcoef
      _ = r * ((q - 1) * S) := by ring
  have hscaled : r * ((q - 1) * S) < r * q ^ (a + 1) :=
    (Nat.mul_lt_mul_left (by omega)).2 hupper
  have hcancel : q * ((r - 1) * S) < q * (r * q ^ a) := by
    calc
      q * ((r - 1) * S) < r * q ^ (a + 1) := lt_of_le_of_lt hmul hscaled
      _ = q * (r * q ^ a) := by
        rw [pow_succ]
        ring
  have hqpos : 0 < q := by omega
  have hfinal : (r - 1) * S < r * q ^ a :=
    (Nat.mul_lt_mul_left hqpos).1 hcancel
  simpa [S] using hfinal
