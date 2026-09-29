-- Prove2me | solution 1 for OddPerfectNumber.no_odd_perfect_k_one_not_odd_m
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:52:16.703406+00:00
-- url     : https://prove2.me/submissions/5a07fe2f-bf18-4a7d-98f4-dd0b19b424cf

import Mathlib

theorem solution (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_not_odd : ¬ Odd m) : n != p * m ^ 2 := by
  -- The target conclusion is boolean `bne`, so prove the `Ne` version in a
  -- `have` (no `intro` on a `Bool` goal) and convert with `bne_iff_ne`.
  have hne : n ≠ p * m ^ 2 := by
    intro h
    have hm_even : Even m := Nat.not_odd_iff_even.mp hm_not_odd
    obtain ⟨k, hk⟩ := hm_even
    have hev : Even (p * m ^ 2) := by
      refine ⟨p * m * k, ?_⟩
      rw [hk]
      ring
    rw [←h] at hev
    exact (Nat.not_even_iff_odd.mpr hodd) hev
  exact bne_iff_ne.mpr hne
