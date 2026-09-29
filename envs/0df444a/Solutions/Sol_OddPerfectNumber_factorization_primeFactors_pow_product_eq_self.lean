-- Prove2me | solution 1 for OddPerfectNumber.factorization_primeFactors_pow_product_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T15:52:14.758847+00:00
-- url     : https://prove2.me/submissions/026b105c-0226-43de-bf69-2ed4aef7b980

import Mathlib

theorem solution (n : Nat)
    (hn : n ≠ 0) :
    (∏ q ∈ n.primeFactors, q ^ n.factorization q) = n := by
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  exact h
