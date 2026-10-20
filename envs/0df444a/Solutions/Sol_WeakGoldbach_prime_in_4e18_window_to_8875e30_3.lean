-- Prove2me | solution 3 for WeakGoldbach.prime_in_4e18_window_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:44:23.172586+00:00
-- url     : https://prove2.me/submissions/2aedf457-acb3-41c7-a68e-668a290094bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_prime_ladder_to_8875e30_strict
import Theorems.Thm_WeakGoldbach_prime_in_window_of_ladder_strict

theorem solution (x : ℕ)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  obtain ⟨k, p, hprime, h0, hstep, htop⟩ := WeakGoldbach.prime_ladder_to_8875e30_strict
  exact WeakGoldbach.prime_in_window_of_ladder_strict k p hprime h0 hstep htop x hx
