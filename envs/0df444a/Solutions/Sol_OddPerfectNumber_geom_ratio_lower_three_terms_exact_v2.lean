-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_three_terms_exact_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T22:51:10.648776+00:00
-- url     : https://prove2.me/submissions/8feea619-55e7-4c03-9ea3-1935ad63eaab

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (q e : Nat) (he : 1 ≤ e) :
    (q^2 + q + 1) * q^(2*e) ≤
      q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
  have hn : 2 ≤ 2*e := by omega
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le q (2*e) hn
  have hpow1 : q ^ (2*e) = q^2 * q^(2*e-2) := by
    calc
      q ^ (2*e) = q ^ ((2*e-2) + 2) := by congr 1 <;> omega
      _ = q^2 * q^(2*e-2) := by rw [pow_add]; ring
  have hpow2 : q ^ (2*e-1) = q * q^(2*e-2) := by
    calc
      q ^ (2*e-1) = q ^ ((2*e-2) + 1) := by congr 1 <;> omega
      _ = q * q^(2*e-2) := by rw [pow_add]; ring
  have hidentity :
      (q^2 + q + 1) * q^(2*e) =
        q^2 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := by
    calc
      (q^2 + q + 1) * q^(2*e) =
          (q^2 + q + 1) * (q^2 * q^(2*e-2)) := by rw [hpow1]
      _ = q^2 * (q^2 * q^(2*e-2) + q * q^(2*e-2) + q^(2*e-2)) := by ring
      _ = q^2 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := by
        rw [← hpow1, ← hpow2]
  have hscaled := Nat.mul_le_mul_left (q*q) hlast
  calc
    (q^2 + q + 1) * q^(2*e) ≤
        q^2 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := le_of_eq hidentity
    _ ≤ q^2 * (∑ i ∈ Finset.range (2*e + 1), q^i) := by
      simpa [pow_two] using hscaled
