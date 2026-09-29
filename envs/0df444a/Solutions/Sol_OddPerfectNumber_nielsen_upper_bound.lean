-- Prove2me | solution 1 for OddPerfectNumber.nielsen_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T06:30:09.293234+00:00
-- url     : https://prove2.me/submissions/294beb2e-3c7c-43b7-91f3-a64c91bf8918

import Theorems.Thm_OddPerfectNumber_nielsen_diophantine_bound

open Finset

/-- **Nielsen (2003).** An odd perfect number `n` satisfies `n < 2 ^ (4 ^ ω(n))`.

This is the specialisation to `n/d = 2/1` of Nielsen's bound for the Diophantine
equation `d * ∏ (∑_{j ≤ e i} x i ^ j) = n * ∏ x i ^ e i`, applied with `X` the set of
prime divisors of `n` and `e` its factorisation exponents. -/
theorem solution (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    n < 2 ^ (4 ^ n.primeFactors.card) := by
  have hpos : 0 < n := hn.2
  have hne : n ≠ 0 := hpos.ne'
  -- `n` is `2/1`-perfect: the sum of its divisors is `2 * n`.
  have hsum : ∑ i ∈ n.divisors, i = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hn
  have hone : 1 < n := by
    rcases Nat.eq_or_lt_of_le hpos with h | h
    · exfalso; rw [← h] at hsum; simp at hsum
    · exact h
  have hXne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hone
  -- The prime factorisation of `n`.
  have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hne]
    rw [Finsupp.prod]
    exact Finset.prod_congr n.support_factorization.symm fun _ _ => rfl
  -- Multiplicativity of `σ` turns `σ n = 2 n` into the Diophantine equation with `d = 1`, `n = 2`.
  have heq : 1 * ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p + 1), p ^ j
      = 2 * ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [one_mul, hfac, ← Nat.sum_divisors hne, hsum]
  have key := OddPerfectNumber.nielsen_diophantine_bound 2 1 n.primeFactors n.factorization
    (by norm_num) (by norm_num) hXne
    (fun p hp => hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hne
      (Nat.dvd_of_mem_primeFactors hp))
    heq
  rw [hfac] at key
  have hprodpos : 0 < (∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Nat.mul_pos (Finset.prod_pos fun p hp => ?_) (Finset.prod_pos fun p hp => ?_)
    · exact (Nat.prime_of_mem_primeFactors hp).pos
    · have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
  have hexp : (2 : ℕ) ^ 2 ^ (2 * n.primeFactors.card) = 2 ^ 4 ^ n.primeFactors.card := by
    congr 1
    rw [pow_mul]
    norm_num
  calc n ≤ n * (2 * ((∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1))) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos (by norm_num) hprodpos)
    _ < 2 ^ 4 ^ n.primeFactors.card := by
        rw [← hexp]; simpa using key
