-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T13:59:28.329984+00:00
-- url     : https://prove2.me/submissions/334abfdd-89e2-4c48-865a-b4e5ad883196

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1

-- EXPONENT CONVENTION: half exponents a,b,c,e; full floors 8,6,4,2.
-- Reduced small-D arm: D<q4 and the half-exponent floors remain explicit.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
    m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq
    hq4prime hq4gt hDq hDsupport ha hb hc he
  rcases hcases with h27 | hrest
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
      m a b c e D p q4 sigma hfac hsigma hrel h27 hp_eq hq4prime hq4gt ha hb hc he
  · rcases hrest with h45 | hrest
    · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
        m a b c e D p q4 sigma hfac hsigma hrel (Or.inl h45) hp_eq hq4prime hDq ha hb hc he
    · rcases hrest with h69 | h75
      · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
          m a b c e D p q4 sigma hfac hsigma hrel (Or.inr h69) hp_eq hq4prime hDq ha hb hc he
      · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D75_absurd_v1
          m a b c e D p q4 sigma hfac hsigma hrel h75 hp_eq hq4prime hDq
