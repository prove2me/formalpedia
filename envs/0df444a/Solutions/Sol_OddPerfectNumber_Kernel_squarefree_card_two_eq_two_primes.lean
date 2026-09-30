-- Prove2me | solution 1 for OddPerfectNumber.Kernel.squarefree_card_two_eq_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:49:16.871974+00:00
-- url     : https://prove2.me/submissions/c1c36184-e5a0-4e7e-99a8-66b6e4b2af82

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem solution {d : Nat} (hdsf : Squarefree d)
    (hcard : d.primeFactors.card = 2) :
    ∃ q r : Nat, q < r ∧ q.Prime ∧ r.Prime ∧ d = q * r := by
  obtain ⟨q, r, hqr, hset⟩ := Finset.card_eq_two.mp hcard
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := d) (by simp [hset])
  have hr : r.Prime := Nat.prime_of_mem_primeFactors (n := d) (by simp [hset])
  have hd : d = q * r := by
    simpa [hset, hqr] using (Nat.prod_primeFactors_of_squarefree hdsf).symm
  rcases lt_or_gt_of_ne hqr with hlt | hlt
  · exact ⟨q, r, hlt, hq, hr, hd⟩
  · exact ⟨r, q, hlt, hr, hq, by simpa [Nat.mul_comm] using hd⟩

