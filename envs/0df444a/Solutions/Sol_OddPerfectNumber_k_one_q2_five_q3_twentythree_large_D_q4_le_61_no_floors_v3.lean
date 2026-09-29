-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_le_61_no_floors_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:09:53.617863+00:00
-- url     : https://prove2.me/submissions/58b38dab-24c1-42a4-bb05-2f0d1e38a31e

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents. No floors are needed.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 111 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) : q4 ≤ 61 := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu23 := OddPerfectNumber.geom_sum_cross_lt_of_le 23 23 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    (by omega) (by rfl) hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5)
    (Nat.mul_lt_mul_of_lt_of_lt hu23 huq)
  have hupper : 176 * (q4 - 1) * sigma < 345 * q4 * m ^ 2 := by
    calc
      176 * (q4 - 1) * sigma =
          (2*S3) * (4*S5) * (22*S23) * ((q4-1)*Sq) := by
            rw [hsigma]
            dsimp [S3, S5, S23, Sq]
            ring
      _ < (3*3^(2*a)) * (5*5^(2*b)) *
          ((23*23^(2*c)) * (q4*q4^(2*e))) := by
            simpa [S3, S5, S23, Sq, Nat.mul_assoc] using hu
      _ = 345 * q4 * m ^ 2 := by rw [hfac]; ring
  have hcoef : 176 * (q4 - 1) * p < 345 * q4 * D := by
    have hDpos : 0 < D := by omega
    have hineq : 176 * (q4 - 1) * p * m ^ 2 <
        345 * q4 * D * m ^ 2 := by
      calc
        176 * (q4 - 1) * p * m ^ 2 =
            176 * (q4 - 1) * (p * m ^ 2) := by ring
        _ = 176 * (q4 - 1) * (D * sigma) := by rw [hrel]
        _ = D * (176 * (q4 - 1) * sigma) := by ring
        _ < D * (345 * q4 * m ^ 2) :=
          (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = 345 * q4 * D * m ^ 2 := by ring
    exact Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineq)
  rw [hp_eq] at hcoef
  by_contra hq4le
  have hq4ge62 : 62 ≤ q4 := by omega
  have hq4ge67 : 67 ≤ q4 := by
    by_contra hbad
    have hq4le66 : q4 ≤ 66 := by omega
    interval_cases q4 <;> norm_num at hq4prime
  have hratio : 64 * q4 ≤ 65 * (q4 - 1) := by omega
  have hlin : 65 * 345 * D ≤ 176 * 64 * (2 * D - 1) := by omega
  have hlinq : 65 * 345 * q4 * D ≤
      176 * 64 * q4 * (2 * D - 1) := by
    have := Nat.mul_le_mul_right q4 hlin
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
  have hleft : 176 * 64 * q4 * (2 * D - 1) ≤
      65 * 176 * (q4 - 1) * (2 * D - 1) := by
    have := Nat.mul_le_mul_right (176 * (2 * D - 1)) hratio
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
  have hright : 65 * 176 * (q4 - 1) * (2 * D - 1) <
      65 * 345 * q4 * D := by
    calc
      65 * 176 * (q4 - 1) * (2 * D - 1) =
          65 * (176 * (q4 - 1) * (2 * D - 1)) := by ring
      _ < 65 * (345 * q4 * D) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 65)).2 hcoef
      _ = 65 * 345 * q4 * D := by ring
  have : 65 * 345 * q4 * D < 65 * 345 * q4 * D :=
    lt_of_le_of_lt hlinq (lt_of_le_of_lt hleft hright)
  omega
