-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_685_v5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T12:47:17.339555+00:00
-- url     : https://prove2.me/submissions/a1f1d73d-2a64-434b-9c39-6074b1264f15

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt47 : 47 < q4)
    (hq4le : q4 ≤ 61) (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    D ≤ 685 := by
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
      _ = 345 * q4 * m ^ 2 := by
        rw [hfac]
        ring
  have hcoef : 176 * (q4 - 1) * p < 345 * q4 * D := by
    have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
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
  have hq4cases :=
    OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_cases
      q4 hq4prime hq4gt47 hq4le
  rcases hq4cases with h53 | h59 | h61
  · subst q4
    rcases hq4dvd with ⟨k, hk⟩
    by_contra hbad
    have hklo : 3 ≤ k := by omega
    have hkhi : k ≤ 18 := by
      rw [hk] at hcoef
      norm_num at hcoef
      omega
    have hk13 : 13 ≤ k := by omega
    have hkc : k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hkc with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num [hk, hp_eq] at hp
    · norm_num [hk] at hDodd
    · norm_num [hk, hp_eq] at hp
    · norm_num [hk] at hDodd
    · have hs := hDsupport 17 (by norm_num) (by norm_num [hk])
      norm_num at hs
    · norm_num [hk] at hDodd
  · subst q4
    rcases hq4dvd with ⟨k, hk⟩
    rw [hk] at hcoef
    norm_num at hcoef
    omega
  · subst q4
    rcases hq4dvd with ⟨k, hk⟩
    rw [hk] at hcoef
    norm_num at hcoef
    omega
