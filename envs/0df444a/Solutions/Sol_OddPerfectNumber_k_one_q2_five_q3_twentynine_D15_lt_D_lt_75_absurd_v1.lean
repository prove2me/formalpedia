-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T14:30:28.231671+00:00
-- url     : https://prove2.me/submissions/d3a11eb7-c5cb-489b-8659-fada8a31bacf

import Mathlib.Tactic
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4

theorem solution (m d D p q4 sigma a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDgt : 15 < D) (hDlt : D < 75)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hp4 : p % 4 = 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e)
    (hD45q4 : D = 45 → q4 = 31 ∨ q4 = 41) : False := by
  have ha4 : 4 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  have hc2 : 2 ≤ c := by omega
  have he1 : 1 ≤ e := by omega
  exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
    m d D p q4 sigma a b c e hfac hsigma hrel hDgt hDlt hDodd hp hp_eq hp4
    hq4prime hq4gt hDsupport hm0 hsig hglobal hddvd hsupport ha4 hb3 hc2 he1
