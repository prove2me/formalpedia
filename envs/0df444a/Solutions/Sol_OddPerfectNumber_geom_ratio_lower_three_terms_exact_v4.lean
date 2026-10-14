-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_terms_exact_v4
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-17T06:23:26.00697+00:00
-- url     : https://prove2.me/submissions/f753831b-5227-47a7-a612-4741e6fd4ed8

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (q e : Nat) (he : 1 ≤ e) : (q^2 + q + 1) * q^(2*e) ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  have h2e : 2 ≤ 2 * e := by omega
  have key := OddPerfectNumber.geom_sum_last_three_terms_le q (2*e) h2e
  have expand : q^2 * (q ^ (2*e) + q ^ (2*e - 1) + q ^ (2*e - 2)) = (q^2 + q + 1) * q^(2*e) := by
    have h1 : (2 : ℕ) + (2*e - 1) = 1 + 2*e := by omega
    have h2 : (2 : ℕ) + (2*e - 2) = 2*e := by omega
    have hq1 : q^2 * q^(2*e - 1) = q^(1 + 2*e) := by rw [← pow_add, h1]
    have hq2 : q^2 * q^(2*e - 2) = q^(2*e) := by rw [← pow_add, h2]
    have hq3 : q^(1 + 2*e) = q * q^(2*e) := by rw [pow_add, pow_one]
    rw [mul_add, mul_add, hq1, hq2, hq3]
    ring
  calc (q^2 + q + 1) * q^(2*e)
      = q^2 * (q ^ (2*e) + q ^ (2*e - 1) + q ^ (2*e - 2)) := expand.symm
    _ ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
        apply Nat.mul_le_mul_left
        exact key
