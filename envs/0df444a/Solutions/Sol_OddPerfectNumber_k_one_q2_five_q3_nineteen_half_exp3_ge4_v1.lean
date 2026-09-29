-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T10:40:18.180741+00:00
-- url     : https://prove2.me/submissions/c14f124a-1a53-4e25-9ce0-2277536662f6

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_1093_role
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_no_five
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_product_no_five

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    4 ≤ a := by
  obtain ⟨ha3, hb3⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
      hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  by_contra hsmall
  have haeq : a = 3 := by omega
  have hx : (m ^ 2).factorization 3 = 6 := by simpa [haeq] using h3exp
  have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_1093_role
    p m d q4 hp hm hpm hprod hsig hsupport h3mem hx
  have hqge : 547 ≤ q4 := by
    rcases hrole with hp1093 | hq1093
    · have hprod547 : m ^ 2 = 547 * d := by simpa [hp1093] using hprod
      have h547sq : 547 ∣ m ^ 2 := by rw [hprod547]; exact dvd_mul_right 547 d
      have h547prime : Nat.Prime 547 := by norm_num
      have h547m : 547 ∣ m := h547prime.dvd_of_dvd_pow h547sq
      have hm0 : m ≠ 0 := by rcases hm with ⟨u, hu⟩; omega
      have hmem : 547 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h547prime, h547m, hm0⟩
      have hs := hsupport 547 hmem
      rcases hs with h3 | h5 | h19 | hq
      · norm_num at h3
      · norm_num at h5
      · norm_num at h19
      · omega
    · omega
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 547 q4 (2*e)
    (by norm_num) hqge hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5) (Nat.mul_lt_mul_of_lt_of_lt hu19 huq)
  have hupper : 78624 * sigma < 155895 * m ^ 2 := by
    calc
      78624 * sigma =
          ((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
           (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
          ((18 * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i)) *
           (546 * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))) := by rw [hsigma]; ring
      _ < ((3 * 3^(2*a)) * (5 * 5^(2*b))) *
          ((19 * 19^(2*c)) * (547 * q4^(2*e))) := by simpa using hu
      _ = 155895 * m ^ 2 := by rw [hfac]; ring
  have hpd : sigma = p * d := hglobal.trans hsig
  have hp2 := hp.two_le
  have hDpos : 0 < (p + 1) / 2 := by omega
  have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by rw [hpd, hprod]; ring
  have hmul : (78624 * p) * m ^ 2 < (155895 * ((p + 1) / 2)) * m ^ 2 := by
    calc
      (78624 * p) * m ^ 2 = 78624 * (p * m ^ 2) := by ring
      _ = 78624 * (((p + 1) / 2) * sigma) := by rw [hrel]
      _ = ((p + 1) / 2) * (78624 * sigma) := by ring
      _ < ((p + 1) / 2) * (155895 * m ^ 2) := (Nat.mul_lt_mul_left hDpos).2 hupper
      _ = (155895 * ((p + 1) / 2)) * m ^ 2 := by ring
  have hcoef := Nat.lt_of_mul_lt_mul_right hmul
  have hD : (p + 1) / 2 < 59 := by omega
  rcases hrole with hp1093 | hq1093
  · omega
  · subst q4
    have h5pow : 5 ^ 6 ∣ 5 ^ (2*b) := pow_dvd_pow 5 (by omega)
    have h5fac : 5 ^ (2*b) ∣ m ^ 2 := by
      rw [hfac]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have h5sig := OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
      p m d sigma hp hprod hpd (by omega) (h5pow.trans h5fac)
    have hno := OddPerfectNumber.q2_five_q3_nineteen_q4_1093_product_no_five
      (2*a) (2*b) (2*c) (2*e)
      (OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three_v2 a)
      (OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_v2 c)
      (OddPerfectNumber.q2_five_q3_nineteen_q4_1093_no_five e)
    exact hno (by rw [← hsigma]; exact h5sig)
