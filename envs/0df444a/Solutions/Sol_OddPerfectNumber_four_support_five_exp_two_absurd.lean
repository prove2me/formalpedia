-- Prove2me | solution 1 for OddPerfectNumber.four_support_five_exp_two_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:48:19.543067+00:00
-- url     : https://prove2.me/submissions/b56a68cf-6ab6-4066-b075-e803bd643cd9

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_external_thirty_one_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hlocal : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have h31local : 31 ∣ ∑ i ∈ Finset.range (2 + 1), 5 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h31global : 31 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h31local hlocal
  exact OddPerfectNumber.four_support_external_thirty_one_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt h31global
