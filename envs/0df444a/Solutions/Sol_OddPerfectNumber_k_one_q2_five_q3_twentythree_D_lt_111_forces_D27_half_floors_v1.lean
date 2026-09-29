-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:29:09.231604+00:00
-- url     : https://prove2.me/submissions/d3bae087-86c7-46d4-908b-dd934eb61ac4

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D = 27 := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
    D p q4 hDlt hDodd hp hp_eq hq4gt hDq hDsupport
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
        m a b c e 3 p q4 sigma hfac hsigma hrel (Or.inl rfl) hp_eq ha hb hc he)
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
        m a b c e 9 p q4 sigma hfac hsigma hrel (Or.inr (Or.inl rfl)) hp_eq ha hb hc he)
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
        m a b c e 15 p q4 sigma hfac hsigma hrel (Or.inr (Or.inr rfl)) hp_eq ha hb hc he)
  · rfl
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
        m a b c e 45 p q4 sigma hfac hsigma hrel (Or.inl rfl) hp_eq hq4prime hDq ha hb hc he)
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
        m a b c e 69 p q4 sigma hfac hsigma hrel (Or.inr rfl) hp_eq hq4prime hDq ha hb hc he)
  · exact False.elim
      (OddPerfectNumber.k_one_q2_five_q3_twentythree_D75_absurd_v1
        m a b c e 75 p q4 sigma hfac hsigma hrel rfl hp_eq hq4prime hDq)
