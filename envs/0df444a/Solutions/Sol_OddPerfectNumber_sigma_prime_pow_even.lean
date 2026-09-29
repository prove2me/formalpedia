-- Prove2me | solution 1 for OddPerfectNumber.sigma_prime_pow_even
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:48:17.95193+00:00
-- url     : https://prove2.me/submissions/11f993fc-3569-44f2-bcd5-bb04356be2ef

import Mathlib

-- STAGED, NOT YET SUBMITTED.
-- Shares the mod-2 divisor-sum pattern with the k=9 evenness proof
-- (candidate 429, pending repair of 428's embedding-coe CE). Submit only
-- after 429 ACCEPTs; both files now use the `show` + `sum_const_nat`
-- shape per the row-428 regression test.
theorem solution (p k : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk4 : k % 4 = 1) : Even (∑ d ∈ (p ^ k).divisors, d) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Nat.divisors_prime_pow hp k]
  simp only [Finset.sum_map]
  rw [Nat.even_iff, Finset.sum_nat_mod]
  show (∑ i ∈ Finset.range (k + 1), p ^ i % 2) % 2 = 0
  have h1 : ∀ i ∈ Finset.range (k + 1), p ^ i % 2 = 1 := by
    intro i _
    exact Nat.odd_iff.mp (hodd.pow)
  -- `sum_const_nat` keeps the sum as `card * 1`, avoiding the `•`
  -- eliminator entirely (verified name in BigOperators/Group/Finset/Basic).
  have h2 : (∑ i ∈ Finset.range (k + 1), p ^ i % 2)
      = (Finset.range (k + 1)).card * 1 :=
    Finset.sum_const_nat h1
  rw [h2, Finset.card_range, mul_one]
  omega
