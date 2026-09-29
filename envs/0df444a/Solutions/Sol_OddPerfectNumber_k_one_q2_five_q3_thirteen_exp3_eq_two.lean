-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:20:52.180302+00:00
-- url     : https://prove2.me/submissions/4298c02b-a48d-4823-ab54-21ea769b3441

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

/-
`a` is the 3-adic exponent of `m ^ 2` in the q2 = 5, q3 = 13 four-support
branch.  It is even and at least `2`, so the only alternative to `a = 2` is
`a ≥ 4`.  The imported abundance lemma
`k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd` rules that out:
with `a ≥ 4`, `b ≥ 2`, `c ≥ 2` the cross-multiplied geometric ratios give
`2 * 81 * 25 * 169 < 121 * 31 * 183`, i.e. `sigma > 2 * m ^ 2`, contradicting
`hupper`.  Its last side condition `q4 ^ e ≤ ∑ i ∈ range (e+1), q4 ^ i` is
exactly the imported `geom_sum_last_term_le`.
-/
theorem solution (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha2 : 2 ≤ a) (haeven : Even a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 := by
  by_contra hne
  have hmod : a % 2 = 0 := Nat.even_iff.mp haeven
  have ha4 : 4 ≤ a := by omega
  exact OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
    m a b c e q4 sigma hfac hsigma hupper ha4 hb hc
    (OddPerfectNumber.geom_sum_last_term_le q4 e)
