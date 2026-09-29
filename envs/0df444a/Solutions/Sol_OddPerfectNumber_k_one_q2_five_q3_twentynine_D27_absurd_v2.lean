-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:51:09.487402+00:00
-- url     : https://prove2.me/submissions/b3573de3-459c-4046-aa58-acde02d5d690

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_cases_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_absurd_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_q4_53_absurd_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_exception_absurd_v1

theorem solution (m d sigma D p q4 a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 27)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) : False := by
  have hq4le := OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
    m a b c e D p q4 sigma hfac hsigma hrel hD hp hp_eq hq4prime hq4gt ha hb hc he
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_cases_v1
    q4 hq4prime hq4gt hq4le
  rcases hcases with h31 | h37 | h41 | h43 | h47 | h53 | h59 | h61 | h67 | h71 | h73 | h79 | h83 | h89
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma (Or.inl h31)
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma (Or.inr (Or.inl h37))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inl h41)))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inl h43))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_exception_absurd_v1
      m d sigma D p q4 a b c e hsigma hrel hD hp_eq (Or.inl h47)
      hsig hddvd hm0 hglobal hsupport
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_q4_53_absurd_v1
      D p sigma m a b c e q4 hrel hD hp_eq hsigma h53
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h59)))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h61))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h67)))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h71))))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h73)))))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h79))))))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
      D p sigma m a b c e q4 hrel hD hp_eq hsigma
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h83))))))))))
  · exact OddPerfectNumber.q2_five_q3_twentynine_D27_exception_absurd_v1
      m d sigma D p q4 a b c e hsigma hrel hD hp_eq (Or.inr h89)
      hsig hddvd hm0 hglobal hsupport
