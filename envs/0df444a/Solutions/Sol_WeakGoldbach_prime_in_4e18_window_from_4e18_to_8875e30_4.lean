-- Prove2me | solution 4 for WeakGoldbach.prime_in_4e18_window_from_4e18_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:36:51.151931+00:00
-- url     : https://prove2.me/submissions/0e53c763-ff2b-4f87-8a6f-d5376cbec8f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_4e18_to_1e26
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_1e26_to_8875e30

set_option autoImplicit false

/-- Helfgott–Platt's computational window split at $10^{26}$ (binary-verified vs. high ladder). -/
theorem solution (x : ℕ)
    (hxl : 4 * 10 ^ 18 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  by_cases h : x ≤ 10 ^ 26
  · exact WeakGoldbach.prime_in_4e18_window_4e18_to_1e26 x hxl h
  · have h26 : 10 ^ 26 ≤ x := Nat.le_of_lt (Nat.not_le.mp h)
    exact WeakGoldbach.prime_in_4e18_window_1e26_to_8875e30 x h26 hx

#print axioms solution
