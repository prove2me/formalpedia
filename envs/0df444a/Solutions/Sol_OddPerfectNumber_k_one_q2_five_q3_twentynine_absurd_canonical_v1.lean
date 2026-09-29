-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_absurd_canonical_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:33:19.674219+00:00
-- url     : https://prove2.me/submissions/417457d5-be0d-490c-8e5b-15235bd53f20

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_half_exponent_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_v7
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_absurd_v3

theorem solution (p m d q4 a b c e sigma D : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
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
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hDrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hDodd : Odd D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hddvd : d ∣ m ^ 2) : False := by
  obtain ⟨ha4, hb3, hc2, he1⟩ :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_half_exponent_floors_v1
      p m d q4 a b c e sigma hp hp4 hm hpm hprod hsig hsupport
      hq4prime hq4gt hfac hsigma hglobal h3mem h3exp h5mem h5exp
      h29mem h29exp ha hb hc he
  have hDgt :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v7
      m a b c e D p q4 sigma hfac hsigma hDrel hp hp_eq hq4gt
      ha4 hb3 hc2 he1
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, rfl⟩
    omega
  by_cases hlt : D < 75
  · exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
      m d D p q4 sigma a b c e hfac hsigma hDrel hDgt hlt hDodd hp
      hp_eq hp4 hq4prime hq4gt hDsupport hm0 hsig hglobal hddvd
      hsupport ha4 hb3 hc2 he1
  · have hDlow : 75 ≤ D := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hDrel hDlow hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha4 hb3 hc2 he1
