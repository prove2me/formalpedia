-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T02:06:31.256523+00:00
-- url     : https://prove2.me/submissions/dd8d23fc-579c-4454-b79e-689d30f88d24

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_canonical_absurd_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    False := by
  have hD27 := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_v1
    m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq hq4prime
    hq4gt hDq hDsupport ha hb hc he
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_canonical_absurd_v2
    m a b c e D p q4 sigma hfac hsigma hrel hD27 hp_eq hq4prime hq4gt
    ha hb hc he
