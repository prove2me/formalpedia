-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_mult_prime_exists
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:49:19.10904+00:00
-- url     : https://prove2.me/submissions/14ef8c5f-ff61-4b5e-be1c-794a3940abec

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Push

set_option autoImplicit false
open scoped BigOperators

theorem solution {a : Nat} (ha0 : a ≠ 0) (hna : ¬ ∃ y, y ^ 2 = a) :
    ∃ t : Nat, t.Prime ∧ t ∣ a ∧ ¬ Even (a.factorization t) := by
  by_contra h
  push Not at h
  apply hna
  refine ⟨∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2), ?_⟩
  calc
    (∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)) ^ 2 =
        ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2 * 2) := by
      rw [← Finset.prod_pow]
      simp_rw [← pow_mul]
    _ = ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.div_mul_cancel (even_iff_two_dvd.mp
        (h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)))]
    _ = a := (Nat.prod_primeFactors_pow_factorization ha0).symm

