-- Prove2me | solution 7 for WeakGoldbach.prime_in_4e18_window_from_4e18_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:44:24.837985+00:00
-- url     : https://prove2.me/submissions/8f1bbe24-ea47-4411-a834-297a703a7a44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_prime_ladder_to_8875e30_strict
import Theorems.Thm_WeakGoldbach_prime_in_window_of_ladder_strict

theorem solution (x : ℕ) (_hxl : 4 * 10 ^ 18 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  obtain ⟨k, p, hprime, h0, hstep, htop⟩ := WeakGoldbach.prime_ladder_to_8875e30_strict
  exact WeakGoldbach.prime_in_window_of_ladder_strict k p hprime h0 hstep htop x hx
