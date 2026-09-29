-- Prove2me | solution 1 for OddPerfectNumber.four_support_five_exp_four_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:41:51.382088+00:00
-- url     : https://prove2.me/submissions/f1ee3eeb-ebfe-43c0-bc70-6d6d222c30aa

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_external_eleven_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (hlocal : (∑ i ∈ Finset.range (4 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have h11local : 11 ∣ ∑ i ∈ Finset.range (4 + 1), 5 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h11global : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h11local hlocal
  exact OddPerfectNumber.four_support_external_eleven_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt h11global
