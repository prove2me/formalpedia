-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T11:05:40.733402+00:00
-- url     : https://prove2.me/submissions/bd63bf2c-9f61-4669-9c34-9820d1970f43

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v6

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are 2*a,... .
-- No derived floor, D-range, tuple, order or fourth-prime divisibility premise.
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
    False := by
  have ha4 := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  obtain ⟨_, hb3⟩ := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp ha hb hc he
  have hc2 := OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
    p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp
    h19mem h19exp ha hb hc he
  have hpd : sigma = p * d := hglobal.trans hsig
  have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by
    rw [hpd, hprod]
    ring
  have hDodd : Odd ((p + 1) / 2) := by
    refine ⟨p / 4, ?_⟩
    omega
  have hpeq : p = 2 * ((p + 1) / 2) - 1 := by omega
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨u, hu⟩
    omega
  have hDsupport : ∀ r, r.Prime → r ∣ (p + 1) / 2 →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4 := by
    intro r hr hrd
    have hDdvd : (p + 1) / 2 ∣ m ^ 2 := ⟨d, hprod⟩
    have hrm : r ∣ m := hr.dvd_of_dvd_pow (hrd.trans hDdvd)
    exact hsupport r (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm0⟩)
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v6
    m a b c e ((p + 1) / 2) p q4 sigma hfac hsigma hrel hDodd hp hpeq
    hq4prime hq4gt hDsupport ha4 hb3 hc2 (by omega)
