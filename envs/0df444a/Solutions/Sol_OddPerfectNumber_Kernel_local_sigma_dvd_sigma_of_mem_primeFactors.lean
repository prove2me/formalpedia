-- Prove2me | solution 1 for OddPerfectNumber.Kernel.local_sigma_dvd_sigma_of_mem_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:51:55.486981+00:00
-- url     : https://prove2.me/submissions/9003279c-418f-4943-b0d5-e87bc4bbb541

import Mathlib

open ArithmeticFunction in
theorem opn_local_sigma_aux {n l : Nat} (hn : n != 0)
    (hl : l ∈ n.primeFactors) :
    Dvd.dvd (∑ i ∈ Finset.range (2 * n.factorization l + 1), l ^ i)
      (∑ d ∈ (n ^ 2).divisors, d) := by
  have hn0 : n ≠ 0 := by simpa using hn
  have hp : l.Prime := Nat.prime_of_mem_primeFactors hl
  have hm0 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  have hfac : (n ^ 2).factorization l = 2 * n.factorization l := by
    simp [Nat.factorization_pow]
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self (n ^ 2) l
  have hcop : Nat.Coprime (l ^ (n ^ 2).factorization l) (n ^ 2 / l ^ (n ^ 2).factorization l) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hm0)
  have key : ArithmeticFunction.sigma 1 (n ^ 2) = ArithmeticFunction.sigma 1 (l ^ (n ^ 2).factorization l) *
      ArithmeticFunction.sigma 1 (n ^ 2 / l ^ (n ^ 2).factorization l) := by
    conv_lhs => rw [← hsplit]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [← sigma_one_apply, key, sigma_one_apply_prime_pow hp, hfac]
  exact Dvd.intro _ rfl

theorem solution {n l : Nat} (hn : n != 0)
    (hl : l ∈ n.primeFactors) :
    Dvd.dvd (∑ i ∈ Finset.range (2 * n.factorization l + 1), l ^ i)
      (∑ d ∈ (n ^ 2).divisors, d) := by
  exact opn_local_sigma_aux hn hl
