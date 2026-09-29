-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp3_ne_three_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:36:35.781976+00:00
-- url     : https://prove2.me/submissions/a583b2ff-829b-44cf-b615-6e8db5762e2e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_general_v2
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exp5_ne_two_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≠ 3 := by
  intro ha3
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hb1 := OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_ne_one_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  have hb2 := OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exp5_ne_two_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    hfac hsigma hglobal h3mem h3exp h5mem h5exp h29mem h29exp ha hb hc he
  have hb3 : 3 ≤ b := by omega
  have h6 : (m ^ 2).factorization 3 = 6 := by omega
  have hroles := OddPerfectNumber.k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1
    p m d q4 hp hm hpm hprod hsig hsupport h3mem h6
  have hpd : sigma = p * d := hglobal.trans hsig
  have hDpos : 0 < (p + 1) / 2 := by have := hp.two_le; omega
  have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by rw [hpd, hprod]; ring
  have hDdvd : (p + 1) / 2 ∣ m ^ 2 := ⟨d, hprod⟩
  have hDsupport (r : Nat) (hr : r.Prime) (hrD : r ∣ (p + 1) / 2) :
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4 := by
    exact hsupport r (Nat.mem_primeFactors.mpr
      ⟨hr, hr.dvd_of_dvd_pow (hrD.trans hDdvd), hm0⟩)
  have hqge : 547 ≤ q4 := by
    rcases hroles with hp1093 | hq1093
    · have hd547 : 547 ∣ (p + 1) / 2 := by norm_num [hp1093]
      have hs := hDsupport 547 (by norm_num) hd547
      omega
    · omega
  have u3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2 * a)
    (by norm_num) (by norm_num) (by norm_num)
  have u5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2 * b)
    (by norm_num) (by norm_num) (by norm_num)
  have u29 := OddPerfectNumber.geom_sum_cross_lt_of_le 29 29 (2 * c)
    (by norm_num) (by norm_num) (by norm_num)
  have uq := OddPerfectNumber.geom_sum_cross_lt_of_le 547 q4 (2 * e)
    (by norm_num) hqge hq4prime
  have hu := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt u3 u5) (Nat.mul_lt_mul_of_lt_of_lt u29 uq)
  have hbound : 122304 * sigma < 237945 * m ^ 2 := by
    rw [hfac, hsigma]
    convert hu using 1 <;> ring
  have hmul : (122304 * p) * m ^ 2 < (237945 * ((p + 1) / 2)) * m ^ 2 := by
    calc (122304 * p) * m ^ 2 = 122304 * (p * m ^ 2) := by ring
      _ = 122304 * (((p + 1) / 2) * sigma) := by rw [hrel]
      _ = ((p + 1) / 2) * (122304 * sigma) := by ring
      _ < ((p + 1) / 2) * (237945 * m ^ 2) := (Nat.mul_lt_mul_left hDpos).2 hbound
      _ = (237945 * ((p + 1) / 2)) * m ^ 2 := by ring
  have hcoef := Nat.lt_of_mul_lt_mul_right hmul
  have hDsmall : (p + 1) / 2 < 185 := by omega
  rcases hroles with hp1093 | hq1093
  · omega
  · subst hq1093
    have h5pow : 5 ^ 6 ∣ 5 ^ (2 * b) := pow_dvd_pow 5 (by omega)
    have h5fac : 5 ^ (2 * b) ∣ m ^ 2 := by
      rw [hfac]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have h5sig := OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
      p m d sigma hp hprod hpd hDsmall (h5pow.trans h5fac)
    have h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1 := by
      rw [OddPerfectNumber.order_three_mod_five_eq_four]
      omega
    have h29 : ¬ orderOf (29 : ZMod 5) ∣ 2 * c + 1 := by
      have e29 : (29 : ZMod 5) = 4 := by decide
      rw [e29]
      have h42 : (4 : ZMod 5) ^ 2 = 1 := by decide
      have hdvd : orderOf (4 : ZMod 5) ∣ 2 := orderOf_dvd_of_pow_eq_one h42
      have hne : orderOf (4 : ZMod 5) ≠ 1 :=
        fun hcon => absurd (orderOf_eq_one_iff.mp hcon) (by decide)
      have ho2 : orderOf (4 : ZMod 5) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd h1 hne
        · exact h2
      rw [ho2]
      omega
    have h4 : ¬ orderOf (1093 : ZMod 5) ∣ 2 * e + 1 := by
      have e3 : (1093 : ZMod 5) = 3 := by decide
      rw [e3, OddPerfectNumber.order_three_mod_five_eq_four]
      omega
    exact OddPerfectNumber.k_one_p5_no_local_sigma_source_general_v2
      sigma a b c e 29 1093 hsigma h5sig h3 h29 h4
