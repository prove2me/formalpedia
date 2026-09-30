-- Prove2me | solution 1 for OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:49:17.981979+00:00
-- url     : https://prove2.me/submissions/a75beb5a-1f9e-48c3-afd8-ddd304e2a41f

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {d : Nat} (hdpos : 0 < d)
    (hdsf : Squarefree d) (hne1 : d ≠ 1) (hnePrime : ∀ q, q.Prime → d ≠ q) :
    2 ≤ d.primeFactors.card := by
  by_contra h
  have hc : d.primeFactors.card = 0 ∨ d.primeFactors.card = 1 := by omega
  rcases hc with hc | hc
  · have hset : d.primeFactors = ∅ := Finset.card_eq_zero.mp hc
    have hd : d = 1 := by
      simpa [hset] using (Nat.prod_primeFactors_of_squarefree hdsf).symm
    exact hne1 hd
  · obtain ⟨q, hset⟩ := Finset.card_eq_one.mp hc
    have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := d) (by simp [hset])
    have hd : d = q := by
      simpa [hset] using (Nat.prod_primeFactors_of_squarefree hdsf).symm
    exact hnePrime q hq hd

