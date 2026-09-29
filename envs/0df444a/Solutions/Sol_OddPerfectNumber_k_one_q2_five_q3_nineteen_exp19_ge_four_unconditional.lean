-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T05:44:01.442107+00:00
-- url     : https://prove2.me/submissions/ec248444-314d-4133-b70d-3293a9315c3f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_absurd

theorem solution (p m d q4 sigma a b c e : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsigma_eq : sigma = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = c)
    (h19pos : 0 < c) (h19even : Even c)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (hq4 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    4 ≤ c := by
  by_contra hnot
  have hclt : c < 4 := by omega
  rcases h19even with ⟨k, hk⟩
  have hc2 : c = 2 := by omega
  have h19exp2 : (m ^ 2).factorization 19 = 2 := by omega
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_absurd
    p m d q4 sigma a b c e hp hm hpm hprod hsig hsigma_eq hsupport
    hq4prime hq4gt h19mem h19exp2 hD hpow hsigma h3 h19 hq4
