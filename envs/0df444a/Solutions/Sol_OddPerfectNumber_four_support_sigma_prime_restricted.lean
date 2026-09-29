-- Prove2me | solution 1 for OddPerfectNumber.four_support_sigma_prime_restricted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T10:41:54.944182+00:00
-- url     : https://prove2.me/submissions/83e9e42f-b962-402d-81fe-dcf0b93c042a

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_mem_support_or_euler

theorem solution (p m d q1 q2 q3 q4 r : Nat)
    (hp : p.Prime) (hr : r.Prime) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = q1 ∨ x = q2 ∨ x = q3 ∨ x = q4) :
    r = p ∨ r = q1 ∨ r = q2 ∨ r = q3 ∨ r = q4 := by
  rcases OddPerfectNumber.sigma_prime_mem_support_or_euler
      p m d r hp hr hsig hddvd hrsigma with hrp | hrm
  · exact Or.inl hrp
  · have hrmem : r ∈ m.primeFactors := hr.mem_primeFactors hrm hm0
    rcases hsupport r hrmem with h1 | h2 | h3 | h4
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
