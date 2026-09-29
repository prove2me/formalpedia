-- Prove2me | solution 1 for OddPerfectNumber.two_distinct_odd_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:29:09.4+00:00
-- url     : https://prove2.me/submissions/0dd23750-f401-41d3-9637-c8a2389699eb

import Mathlib

-- STAGED direct proof. Lemma names verified against pinned Mathlib:
-- Finset.one_lt_card (Data/Finset/Card.lean), Finset.mem_erase,
-- Nat.prime_of_mem_primeFactors, Nat.dvd_of_mem_primeFactors,
-- Nat.Prime.odd_of_ne_two (as used in the accepted dvd_succ proof).
theorem solution (k : Nat)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card) :
    ∃ q1 q2, q1 ≠ q2 ∧ q1.Prime ∧ q2.Prime ∧ Odd q1 ∧ Odd q2 ∧
      q1 ∣ k + 1 ∧ q2 ∣ k + 1 := by
  have h1 : 1 < ((k + 1).primeFactors.erase 2).card := by omega
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp h1
  rw [Finset.mem_erase] at ha hb
  obtain ⟨ha2, hamem⟩ := ha
  obtain ⟨hb2, hbmem⟩ := hb
  have hpa : a.Prime := Nat.prime_of_mem_primeFactors hamem
  have hpb : b.Prime := Nat.prime_of_mem_primeFactors hbmem
  exact ⟨a, b, hne, hpa, hpb, hpa.odd_of_ne_two ha2,
    hpb.odd_of_ne_two hb2, Nat.dvd_of_mem_primeFactors hamem,
    Nat.dvd_of_mem_primeFactors hbmem⟩
