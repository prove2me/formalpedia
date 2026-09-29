-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_135_ratio_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T17:33:59.593252+00:00
-- url     : https://prove2.me/submissions/a2c55da2-7f36-4fe6-97d0-e3586187228f

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (q e : Nat) (hqgt : 19 < q) (hqle : q ≤ 135) (he : 1 ≤ e) :
    18361 * q ^ (2*e) ≤
      18225 * (∑ i ∈ Finset.range (2*e + 1), q ^ i) := by
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
  have hq2 : q*q ≤ 135*q := by
    calc
      q*q ≤ q*135 := Nat.mul_le_mul_left q hqle
      _ = 135*q := by ring
  have hq2scaled : 136*(q*q) ≤ 136*(135*q) :=
    Nat.mul_le_mul_left 136 hq2
  have hqscaled : 135*q ≤ 135*135 :=
    Nat.mul_le_mul_left 135 hqle
  have hpoly : 136*(q*q) ≤ 18225*q + 18225 := by
    nlinarith [hq2scaled, hqscaled]
  have hlin : 18361 * q^(2*e) ≤
      18225 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := by
    rw [hpow1, hpow2]
    have hmul := Nat.mul_le_mul_right (q^(2*e-2)) hpoly
    calc
      18361 * (q^2 * q^(2*e-2)) =
          18225 * (q^2 * q^(2*e-2)) +
            136 * (q*q) * q^(2*e-2) := by ring
      _ ≤ 18225 * (q^2 * q^(2*e-2)) +
            (18225*q + 18225) * q^(2*e-2) := by
        exact Nat.add_le_add_left hmul _
      _ = 18225 * (q^2 * q^(2*e-2) +
            q * q^(2*e-2) + q^(2*e-2)) := by ring
  calc
    18361 * q^(2*e) ≤
        18225 * (q^(2*e) + q^(2*e-1) + q^(2*e-2)) := hlin
    _ ≤ 18225 * (∑ i ∈ Finset.range (2*e + 1), q^i) :=
      Nat.mul_le_mul_left 18225 hlast
