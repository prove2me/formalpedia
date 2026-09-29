-- Prove2me | solution 1 for OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:39:05.470345+00:00
-- url     : https://prove2.me/submissions/e0e8c2f4-9a8c-4669-82c8-a404d751c0e6

import Mathlib

theorem solution {d : Nat} (hdpos : 0 < d) (hdsf : Squarefree d) (hne1 : d ≠ 1)
    (hnePrime : ∀ q, q.Prime → d ≠ q)
    (hneTwo : ∀ q r, q.Prime → r.Prime → q < r → d ≠ q * r) :
    3 ≤ d.primeFactors.card := by
  have hprod := Nat.prod_primeFactors_of_squarefree hdsf
  by_contra hlt
  rcases (by omega : d.primeFactors.card = 0 ∨ d.primeFactors.card = 1 ∨
      d.primeFactors.card = 2) with hc | hc | hc
  · rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.prod_empty] at hprod
    exact hne1 hprod.symm
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hc
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq]; exact Finset.mem_singleton_self q)
    rw [hq, Finset.prod_singleton] at hprod
    exact hnePrime q hqp hprod.symm
  · obtain ⟨q, r, hqr, hqr'⟩ := Finset.card_eq_two.1 hc
    have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hqr']; simp)
    have hr : r.Prime := Nat.prime_of_mem_primeFactors (by rw [hqr']; simp)
    rw [hqr', Finset.prod_pair hqr] at hprod
    rcases Nat.lt_or_gt_of_ne hqr with h | h
    · exact hneTwo q r hq hr h hprod.symm
    · exact hneTwo r q hr hq h (by rw [← hprod, mul_comm])
