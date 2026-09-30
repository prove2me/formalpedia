-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_below_4e18
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:56:12.863459+00:00
-- url     : https://prove2.me/submissions/8cff9983-0852-4d03-98f4-b685c1f5c9bc

import Mathlib

theorem solution (x : ℕ) (hx : x ≤ 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  by_cases h0 : x = 0
  · subst h0
    exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨p, hp, hpx, hp2x⟩ := Nat.exists_prime_lt_and_le_two_mul x h0
    refine ⟨p, hpx, ?_, hp⟩
    by_contra h
    have hEq : p = 2 * (4 * 10 ^ 18) := by omega
    have hEven : Even p := ⟨4 * 10 ^ 18, by omega⟩
    rcases hp.eq_two_or_odd' with h2 | hodd
    · omega
    · exact (Nat.not_even_iff_odd.mpr hodd) hEven
