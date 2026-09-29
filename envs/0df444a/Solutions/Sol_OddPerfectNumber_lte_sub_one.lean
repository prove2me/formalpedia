-- Prove2me | solution 1 for OddPerfectNumber.lte_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:15:03.63944+00:00
-- url     : https://prove2.me/submissions/c6b59219-50ba-4065-b95b-20a0eb365d59

import Mathlib

-- STAGED direct proof, verbatim from the accepted DHP toolkit
-- (solution 7809bdb2), republished standalone.
theorem solution {q x n : Nat} (hq : q.Prime) (hq2 : q ≠ 2) (hx : 1 < x)
    (hqx : q ∣ x - 1) (hn : n ≠ 0) :
    padicValNat q (x ^ n - 1) = padicValNat q (x - 1) + padicValNat q n := by
  have : Fact q.Prime := ⟨hq⟩
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hnx : ¬ q ∣ x := by
    intro hdvd
    have h1 : q ∣ x - (x - 1) := Nat.dvd_sub hdvd hqx
    have hx1 : x - (x - 1) = 1 := by omega
    rw [hx1] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  have := padicValNat.pow_sub_pow (p := q) hodd (y := 1) hx (by simpa using hqx) hnx hn
  simpa using this
