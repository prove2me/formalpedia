-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_absurd_canonical_coordinates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T17:16:24.317301+00:00
-- url     : https://prove2.me/submissions/fa00a9c2-d8e6-46cb-b959-a5859f470877

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exponent_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_absurd_v3

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are 2*a,2*b,2*c,2*e.
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
    False := by
  obtain ⟨ha4, hb3, hc2, he1⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exponent_floors_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
      hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp
      h29mem h29exp ha hb hc he
  have hpd : sigma = p * d := hglobal.trans hsig
  have hrel : ((p + 1) / 2) * sigma = p * m ^ 2 := by
    rw [hpd, hprod]; ring
  have hDodd : Odd ((p + 1) / 2) := by
    refine ⟨p / 4, ?_⟩
    omega
  have hpeq : p = 2 * ((p + 1) / 2) - 1 := by omega
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨u, hu⟩
    omega
  have hDsupport : ∀ r, r.Prime → r ∣ (p + 1) / 2 →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4 := by
    intro r hr hrd
    have hDdvd : (p + 1) / 2 ∣ m ^ 2 := ⟨d, hprod⟩
    have hrm : r ∣ m := hr.dvd_of_dvd_pow (hrd.trans hDdvd)
    exact hsupport r (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm0⟩)
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hDgt : 15 < (p + 1) / 2 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_half_floors_v1
      m a b c e ((p + 1) / 2) p q4 sigma hfac hsigma hrel hp hpeq hq4gt ha4 hb3 hc2 he1
  by_cases hlt : (p + 1) / 2 < 75
  · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
      m d ((p + 1) / 2) p q4 sigma a b c e hfac hsigma hrel hDgt hlt hDodd
      hp hpeq hp4 hq4prime hq4gt hDsupport hm0 hsig hglobal hddvd hsupport ha4 hb3 hc2 he1
  · have hge : 75 ≤ (p + 1) / 2 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_absurd_v3
      m a b c e ((p + 1) / 2) p q4 sigma hfac hsigma hrel hge hDodd hp hpeq
      hq4prime hq4gt hDsupport ha4 hb3 hc2 he1
