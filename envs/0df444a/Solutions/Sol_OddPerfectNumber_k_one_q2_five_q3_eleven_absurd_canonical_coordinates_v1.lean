-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_absurd_canonical_coordinates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T03:27:04.457661+00:00
-- url     : https://prove2.me/submissions/c201eba0-b15d-4cf4-adac-7958b5ccbedc

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_absurd_v2

open OddPerfectNumber

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 11 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h11mem : 11 ∈ (m ^ 2).primeFactors)
    (h11exp : (m ^ 2).factorization 11 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    False := by
  have h2 : p % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : Odd p := Nat.odd_iff.mpr h2
  have hhalf : (p + 1) / 2 = k + 1 := by omega
  have hprod' : m ^ 2 = (k + 1) * d := by rw [hhalf] at hprod; exact hprod
  have hsig' : sigma = (2 * k + 1) * d := by
    have : p = 2 * k + 1 := hk
    rw [hglobal, hsig, this]
  have h2m : 2 * m ^ 2 = sigma + d := by rw [hprod', hsig']; ring
  have hupper : sigma ≤ 2 * m ^ 2 := by omega
  have ha2 : 2 ≤ 2 * a := by omega
  have haeven : Even (2 * a) := ⟨a, by ring⟩
  have hb2 : 2 ≤ 2 * b := by omega
  have hc2 : 2 ≤ 2 * c := by omega
  have he2 : 2 ≤ 2 * e := by omega
  exact k_one_q2_five_q3_eleven_absurd_v2 m (2*a) (2*b) (2*c) (2*e) p q4 sigma d
    hfac hsigma hglobal hupper hp hp4 hm hpm hprod hsig hsupport
    hq4prime hq4gt h3mem h3exp ha2 haeven hb2 hc2 he2
