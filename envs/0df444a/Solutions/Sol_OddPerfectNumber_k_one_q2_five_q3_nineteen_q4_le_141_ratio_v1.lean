-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T17:39:48.157279+00:00
-- url     : https://prove2.me/submissions/05c5a5bf-72b5-4828-899a-d2b30043bda4

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (q e : Nat) (hqgt : 19 < q) (hqle : q ≤ 141) (he : 1 ≤ e) :
    20023 * q ^ (2*e) ≤
      19881 * (∑ i ∈ Finset.range (2*e + 1), q ^ i) := by
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
  have hq2 : q*q ≤ 141*q := by
    calc
      q*q ≤ q*141 := Nat.mul_le_mul_left q hqle
      _ = 141*q := by ring
  have hq2scaled : 142*(q*q) ≤ 142*(141*q) :=
    Nat.mul_le_mul_left 142 hq2
  have hqscaled : 141*q ≤ 141*141 :=
    Nat.mul_le_mul_left 141 hqle
  have hpoly : 142*(q*q) ≤ 19881*q + 19881 := by
    nlinarith [hq2scaled, hqscaled]
  have hlin : 20023 * q^(2*e) ≤
      19881 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := by
    rw [hpow1, hpow2]
    have hmul := Nat.mul_le_mul_right (q^(2*e-2)) hpoly
    calc
      20023 * (q^2 * q^(2*e-2)) =
          19881 * (q^2 * q^(2*e-2)) +
            142 * (q*q) * q^(2*e-2) := by ring
      _ ≤ 19881 * (q^2 * q^(2*e-2)) +
            (19881*q + 19881) * q^(2*e-2) := by
        exact Nat.add_le_add_left hmul _
      _ = 19881 * (q^2 * q^(2*e-2) +
            q * q^(2*e-2) + q^(2*e-2)) := by ring
  calc
    20023 * q^(2*e) ≤
        19881 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := hlin
    _ ≤ 19881 * (∑ i ∈ Finset.range (2*e + 1), q^i) :=
      Nat.mul_le_mul_left 19881 hlast
