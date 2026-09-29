-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T20:40:10.288144+00:00
-- url     : https://prove2.me/submissions/97c543e5-4260-4a23-bb60-17101cb86531

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D) (hDlt : D < 225)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hq4gtD : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have hq4two : 2 ≤ q4 := hq4prime.two_le
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    hq4two (by rfl) hq4prime
  have hu35 := Nat.mul_lt_mul_of_lt_of_lt hu3 hu5
  have hu19q := Nat.mul_lt_mul_of_lt_of_lt hu19 huq
  have hu := Nat.mul_lt_mul_of_lt_of_lt hu35 hu19q
  have hupper : 144 * (q4 - 1) * sigma < 285 * q4 * (m ^ 2) := by
    calc
      144 * (q4 - 1) * sigma =
          (2*S3) * (4*S5) * (18*S19) * ((q4-1)*Sq) := by
            rw [hsigma]
            dsimp [S3, S5, S19, Sq]
            ring
      _ < (3*3^(2*a)) * (5*5^(2*b)) *
          ((19*19^(2*c)) * (q4*q4^(2*e))) := by
            simpa [S3, S5, S19, Sq, Nat.mul_assoc] using hu
      _ = 285 * q4 * (m ^ 2) := by
            rw [hfac]
            ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hDpos : 0 < D := by omega
  have hmul := (Nat.mul_lt_mul_left hDpos).2 hupper
  have hstrict :
      144 * (q4 - 1) * p * (m ^ 2) <
        (285 * q4 * D) * (m ^ 2) := by
    calc
      144 * (q4 - 1) * p * (m ^ 2) =
          144 * (q4 - 1) * (p * (m ^ 2)) := by ring
      _ = 144 * (q4 - 1) * (D * sigma) := by rw [hrel]
      _ = D * (144 * (q4 - 1) * sigma) := by ring
      _ < D * (285 * q4 * (m ^ 2)) := by simpa [Nat.mul_assoc] using hmul
      _ = (285 * q4 * D) * (m ^ 2) := by ring
  have hcoef : 144 * (q4 - 1) * p < 285 * q4 * D := by
    exact Nat.lt_of_mul_lt_mul_right hstrict
  rw [hp_eq] at hcoef
  have hDupper : D ≤ 224 := by omega
  by_cases h1 : D ≤ 165
  · interval_cases D <;> norm_num at hcoef hq4gtD <;> norm_num <;> omega
  · have h166 : 166 ≤ D := by omega
    by_cases h2 : D ≤ 184
    · interval_cases D <;> norm_num at hcoef hq4gtD <;> norm_num <;> omega
    · have h185 : 185 ≤ D := by omega
      by_cases h3 : D ≤ 204
      · interval_cases D <;> norm_num at hcoef hq4gtD <;> norm_num <;> omega
      · have h205 : 205 ≤ D := by omega
        interval_cases D <;> norm_num at hcoef hq4gtD <;> norm_num <;> omega
