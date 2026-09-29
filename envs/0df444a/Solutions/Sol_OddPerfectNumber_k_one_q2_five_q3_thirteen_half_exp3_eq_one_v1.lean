-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp3_eq_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:59:38.054078+00:00
-- url     : https://prove2.me/submissions/3097f0f0-efab-4d40-877a-baefdc4bbffd

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_eq_two_v2

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a = 1 := by
  -- EXPONENT CONVENTION: a,b,c,e are half exponents; apply the full-exponent
  -- theorem at doubled variables. Even (2*a) is free; 2*a = 2 gives a = 1.
  have hpodd : p % 2 = 1 := by omega
  have h2 : p + 1 = 2 * ((p + 1) / 2) := by omega
  have hle : p ≤ 2 * ((p + 1) / 2) := by omega
  have hupper : sigma ≤ 2 * m ^ 2 := by
    rw [hglobal, hsig, hprod]
    calc p * d ≤ (2 * ((p + 1) / 2)) * d := Nat.mul_le_mul_right d hle
    _ = 2 * (((p + 1) / 2) * d) := by ring
  have ha2 : 2 ≤ 2 * a := by omega
  have haeven : Even (2 * a) := ⟨a, by ring⟩
  have hb2 : 2 ≤ 2 * b := by omega
  have hc2 : 2 ≤ 2 * c := by omega
  have hfull :=
    OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_eq_two_v2
      m (2*a) (2*b) (2*c) (2*e) q4 sigma hfac hsigma hupper
      ha2 haeven hb2 hc2
  omega
