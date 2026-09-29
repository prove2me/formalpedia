-- Prove2me | solution 1 for OddPerfectNumber.prime_not_dvd_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:27:29.362926+00:00
-- url     : https://prove2.me/submissions/51ba3775-640d-43c6-bd67-2854905ca9b5

import Mathlib

-- STAGED direct proof. Lemma names verified against pinned Mathlib:
-- Nat.Prime.eq_one_or_self_of_dvd (Data/Nat/Prime/Basic.lean),
-- Nat.Prime.ne_one.
theorem solution (p q : Nat)
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    ¬ p ∣ q := by
  intro hdvd
  rcases hq.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp.ne_one h
  · exact hqp h.symm
