-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T23:13:01.882927+00:00
-- url     : https://prove2.me/submissions/d3313b29-a8d5-4382-b7c4-dccb47c95395

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_exp3_eq_two
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_source_dispatch_v3

theorem solution
    (m a b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3expfac : (m ^ 2).factorization 3 = a)
    (ha2 : 2 ≤ a) (haeven : Even a)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  have haeq := OddPerfectNumber.k_one_q2_five_q3_eleven_exp3_eq_two
    m a b c e q4 sigma hfac hsigma hupper hq4prime ha2 haeven hb hc
  rcases haeq with rfl
  have h3exp : (m ^ 2).factorization 3 = 2 := by
    simpa using h3expfac
  exact OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch_v3
    m b c e p q4 sigma d
    (by simpa [mul_assoc] using hfac)
    (by simpa [mul_assoc] using hsigma)
    hglobal hupper hp hp4 hm hpm hprod hsig hsupport hq4prime hq4gt
    h3mem h3exp hb hc he
