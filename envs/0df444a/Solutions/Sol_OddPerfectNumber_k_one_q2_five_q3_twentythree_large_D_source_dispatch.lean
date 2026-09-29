-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_source_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T19:44:35.824857+00:00
-- url     : https://prove2.me/submissions/56ffb83d-c7ca-4ce2-8b0d-a6f4bbd4be4e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_53_no_five_source
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_59_no_five_product
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2

theorem solution
    (p m d sigma a b c e q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hsource :
      (q4 = 53 ∧ 5 ∣ sigma) ∨
      (q4 = 59 ∧ 5 ∣ sigma) ∨
      (q4 = 61 ∧ 131 ∣ ∑ x ∈ (m ^ 2).divisors, x)) :
    False := by
  rcases hsource with h53 | h59 | h61
  · rcases h53 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_53_no_five_source
      sigma a b c e hsigma hdiv
  · rcases h59 with ⟨rfl, hdiv⟩
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_59_no_five_product
      sigma a b c e hsigma hdiv
  · rcases h61 with ⟨rfl, h131⟩
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
      p m d 61 hp hp4 hm0 hsig hddvd hsupport hq4prime rfl h131
