-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_survivors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:55:21.650231+00:00
-- url     : https://prove2.me/submissions/3f59bfb4-7a30-4770-a68b-acf2c6796d2b

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_support_cases_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_abundance_cut

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hpeq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    D = 57 ∨ D = 75 ∨ D = 135 := by
  have hDcases :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_support_cases_v2
      D p q4 hDlt hDodd hp hpeq hq4gt hDq hDsupport
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_abundance_cut
    m a b c e D p q4 sigma hfac hsigma hrel hDcases hpeq hq4prime ha hb hc he
