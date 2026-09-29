-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b_one_q4_le_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T13:05:07.838007+00:00
-- url     : https://prove2.me/submissions/2f720338-52cf-4ac2-bac6-d7bc465ee558

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 31 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 31 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hb1 : b = 1) :
    q4 ≤ 170 := by
  subst hb1
  subst hp29
  have hS5 : (∑ i ∈ Finset.range (2*1 + 1), 5 ^ i) = 31 := by
    norm_num [Finset.sum_range_succ]
  have h5pow : 5 ^ (2*1) = 25 := by norm_num
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu31 := OddPerfectNumber.geom_sum_cross_lt_of_le 31 31 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    (by omega) (by rfl) hq4prime
  have key := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu31) huq
  have hsigS : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * 31 *
      ((∑ i ∈ Finset.range (2*c + 1), 31 ^ i) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) := by
    rw [hsigma, hS5]; ring
  have hfacS : m ^ 2 = (3 ^ (2*a) * (31 ^ (2*c) * q4 ^ (2*e))) * 25 := by
    rw [hfac, h5pow]; ring
  have hupper : 1500 * (q4 - 1) * sigma < 2883 * q4 * m ^ 2 := by
    rw [hsigS, hfacS]
    nlinarith [key]
  have hsig29 : sigma = 29 * d := hglobal.trans hsig
  have hfac15 : m ^ 2 = 15 * d := hprod
  have h2 := hupper
  rw [hsig29, hfac15] at h2
  have e1 : (1500 * (q4 - 1) * 29) * d = 1500 * (q4 - 1) * (29 * d) := by ring
  have e2 : (2883 * q4 * 15) * d = 2883 * q4 * (15 * d) := by ring
  have hcoef := h2
  rw [← e1, ← e2] at hcoef
  have hcancel : 1500 * (q4 - 1) * 29 < 2883 * q4 * 15 :=
    Nat.lt_of_mul_lt_mul_right hcoef
  omega
