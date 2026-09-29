-- Prove2me | solution 1 for OddPerfectNumber.sigma_nine_even_of_odd_prime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:45:19.329649+00:00
-- url     : https://prove2.me/submissions/25a4d42b-a058-427e-ace2-bdc3f181c4c9

import Mathlib

theorem solution (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (∑ d ∈ (p ^ 9).divisors, d) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Nat.divisors_prime_pow hp 9]
  simp only [Finset.sum_map]
  rw [Nat.even_iff, Finset.sum_nat_mod]
  -- `sum_map` leaves the map embedding applied (`⇑⟨..⟩ i`); `show`
  -- restates through that defeq residue so later rewrites match.
  show (∑ i ∈ Finset.range (9 + 1), p ^ i % 2) % 2 = 0
  have h1 : ∀ i ∈ Finset.range (9 + 1), p ^ i % 2 = 1 := by
    intro i _
    exact Nat.odd_iff.mp (hodd.pow)
  -- `sum_const_nat` keeps the sum as `card * 1`, avoiding `•` handling.
  have h2 : (∑ i ∈ Finset.range (9 + 1), p ^ i % 2)
      = (Finset.range (9 + 1)).card * 1 :=
    Finset.sum_const_nat h1
  -- NOTE: no trailing `omega` here. After the rewrites the goal is the
  -- ground identity `(9 + 1) % 2 = 0`, which `rw` closes by `rfl`
  -- automatically; an extra tactic errors with "No goals".
  rw [h2, Finset.card_range, mul_one]
