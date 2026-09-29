-- Prove2me | solution 1 for OddPerfectNumber.local_sigma_factor_dvd_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:50:58.441095+00:00
-- url     : https://prove2.me/submissions/51910fb6-1aa8-400d-9c0d-27392f790cc2

import Mathlib

theorem solution (n q : Nat)
    (hn : n ≠ 0) (hq : q ∈ n.primeFactors) :
    (∑ i ∈ Finset.range (n.factorization q + 1), q ^ i) ∣
      ∑ x ∈ n.divisors, x := by
  have hsum : (∑ x ∈ n.divisors, x) = ArithmeticFunction.sigma 1 n :=
    (ArithmeticFunction.sigma_one_apply n).symm
  have hprod : ArithmeticFunction.sigma 1 n =
      ∏ r ∈ n.primeFactors,
        ∑ i ∈ Finset.range (n.factorization r + 1), r ^ i := by
    simpa only [mul_one] using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := n) hn
  rw [hsum, hprod]
  exact Finset.dvd_prod_of_mem
    (fun r => ∑ i ∈ Finset.range (n.factorization r + 1), r ^ i) hq
