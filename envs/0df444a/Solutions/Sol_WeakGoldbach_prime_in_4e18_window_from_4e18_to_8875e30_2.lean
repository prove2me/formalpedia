-- Prove2me | solution 2 for WeakGoldbach.prime_in_4e18_window_from_4e18_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:04:24.252702+00:00
-- url     : https://prove2.me/submissions/f9c5e40a-ae25-4c5e-9d50-3601e124b793
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_4e18_to_1e26
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_1e26_to_8875e30

namespace WeakGoldbach

theorem _root_.solution (x : ℕ)
    (hxl : 4 * 10 ^ 18 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  by_cases h : x ≤ 10 ^ 26
  · exact WeakGoldbach.prime_in_4e18_window_4e18_to_1e26 x hxl h
  · exact WeakGoldbach.prime_in_4e18_window_1e26_to_8875e30 x (by omega) hx

end WeakGoldbach

#print axioms solution
