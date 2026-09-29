-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:20:42.55907+00:00
-- url     : https://prove2.me/submissions/fecff8f9-da8a-4867-a289-25736f5f2dbe

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_D45_D69_D75_q4_le_D_absurd_v1

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4notdiv : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hq4le : q4 ≤ D) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c)
    (he : 1 ≤ e) : False := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
    D p q4 hDlt hDodd hp hp_eq hq4prime hq4gt hq4notdiv hDsupport
  rcases hcases with h3 | h9 | h15 | h27 | h45 | h69 | h75
  · omega
  · omega
  · omega
  · have hfour : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_D45_D69_D75_q4_le_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hfour hp_eq hq4prime hq4le ha hb hc he
  · have hfour : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_D45_D69_D75_q4_le_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hfour hp_eq hq4prime hq4le ha hb hc he
  · have hfour : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_D45_D69_D75_q4_le_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hfour hp_eq hq4prime hq4le ha hb hc he
  · have hfour : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by omega
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_D45_D69_D75_q4_le_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hfour hp_eq hq4prime hq4le ha hb hc he
