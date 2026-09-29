-- Prove2me | solution 1 for OddPerfectNumber.exists_p_source_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:09:58.53377+00:00
-- url     : https://prove2.me/submissions/67f5f5c6-83d9-425b-9100-10382b946b62

import Mathlib

-- STAGED, NOT YET SUBMITTED (awaits publish job c81db585).
-- Every step reuses an accepted-validated pattern (divisor-sum factoring,
-- prime extraction); only the `pow_dvd_pow` descent is new.
theorem solution (p k m : Nat) (hp : p.Prime) (hk : 1 ≤ k)
    (hm2 : m ^ 2 ≠ 0)
    (hdvd : p ^ k ∣ (∑ x ∈ (m ^ 2).divisors, x)) :
    ∃ q ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ (∑ x ∈ (m ^ 2).divisors, x) := by
    have hpk : p ∣ p ^ k := by
      have h : p ^ 1 ∣ p ^ k := pow_dvd_pow p hk
      simpa using h
    exact dvd_trans hpk hdvd
  have hsum : (∑ x ∈ (m ^ 2).divisors, x)
      = ArithmeticFunction.sigma 1 (m ^ 2) :=
    (ArithmeticFunction.sigma_one_apply (m ^ 2)).symm
  have hprod : ArithmeticFunction.sigma 1 (m ^ 2)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
    simpa only [mul_one] using
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) (n := m ^ 2) hm2
  have hσprod : (∑ x ∈ (m ^ 2).divisors, x)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i :=
    hsum.trans hprod
  rw [hσprod] at hpdvd
  obtain ⟨q, hqmem, hqdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpdvd
  exact ⟨q, hqmem, hqdvd⟩
