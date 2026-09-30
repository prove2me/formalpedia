-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_from_4e18_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T04:19:01.03339+00:00
-- url     : https://prove2.me/submissions/6fdc97cb-c4e1-4af2-853f-ec39293392c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_4e18_to_1e26
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_1e26_to_8875e30

theorem solution (x : ℕ) (hxl : 4 * 10 ^ 18 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  by_cases h : x ≤ 10 ^ 26
  · exact WeakGoldbach.prime_in_4e18_window_4e18_to_1e26 x hxl h
  · exact WeakGoldbach.prime_in_4e18_window_1e26_to_8875e30 x (by omega) hx
