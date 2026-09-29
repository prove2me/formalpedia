-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T10:26:44.909931+00:00
-- url     : https://prove2.me/submissions/33a84d27-3e67-4832-824f-37d39adf6324

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_pow_dvd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_127_v2

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents throughout this interface.
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
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    2 ≤ c := by
  obtain ⟨ha3, hb3⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
      hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  by_contra hsmall
  have hc1 : c = 1 := by omega
  subst c
  have hx : (m ^ 2).factorization 19 = 2 := by simpa using h19exp
  have hrole := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_role
    p m d q4 hp hm hpm hprod hsig hsupport h19mem hx
  rcases hrole with hp127 | hq127
  · norm_num [hp127] at hp4
  · subst q4
    have hpd : sigma = p * d := hglobal.trans hsig
    have hpow : 5 ^ 6 ∣ m ^ 2 :=
      OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_pow_dvd
        m (2*a) (2*b) (2*1) (2*e) hfac (by omega)
    have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
      (by norm_num) (by norm_num) (by norm_num)
    have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
      (by norm_num) (by norm_num) (by norm_num)
    have hu127 := OddPerfectNumber.geom_sum_cross_lt_of_le 127 127 (2*e)
      (by norm_num) (by norm_num) (by norm_num)
    have hu := Nat.mul_lt_mul_of_lt_of_lt
      (Nat.mul_lt_mul_of_lt_of_lt hu3 hu5) hu127
    have hus := Nat.mul_lt_mul_of_pos_right hu (by norm_num : 0 < 381 * 361)
    have hs19 : (∑ i ∈ Finset.range (2*1 + 1), (19:Nat)^i) = 381 := by
      norm_num [Finset.sum_range_succ]
    have hupper : 363888 * sigma < 725805 * m ^ 2 := by
      calc
        363888 * sigma =
            (((2 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i)) *
              (4 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i))) *
              (126 * (∑ i ∈ Finset.range (2*e + 1), 127 ^ i))) * (381 * 361) := by
          rw [hsigma, hs19]
          ring
        _ < (((3 * 3^(2*a)) * (5 * 5^(2*b))) * (127 * 127^(2*e))) *
              (381 * 361) := by simpa using hus
        _ = 725805 * m ^ 2 := by rw [hfac]; norm_num; ring
    have hp2 := hp.two_le
    have hDpos : 0 < (p + 1) / 2 := by omega
    have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by
      rw [hpd, hprod]
      ring
    have hmul : (363888 * p) * m ^ 2 < (725805 * ((p + 1) / 2)) * m ^ 2 := by
      calc
        (363888 * p) * m ^ 2 = 363888 * (p * m ^ 2) := by ring
        _ = 363888 * (((p + 1) / 2) * sigma) := by rw [hrel]
        _ = ((p + 1) / 2) * (363888 * sigma) := by ring
        _ < ((p + 1) / 2) * (725805 * m ^ 2) :=
          (Nat.mul_lt_mul_left hDpos).2 hupper
        _ = (725805 * ((p + 1) / 2)) * m ^ 2 := by ring
    have hcoef := Nat.lt_of_mul_lt_mul_right hmul
    have hD : (p + 1) / 2 < 185 := by omega
    exact OddPerfectNumber.q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
      p m d sigma (2*a) (2*b) (2*1) (2*e) hp hprod hpd hD hpow hsigma
      (OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three_v2 a)
      (OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_v2 1)
      (OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_127_v2 e)
