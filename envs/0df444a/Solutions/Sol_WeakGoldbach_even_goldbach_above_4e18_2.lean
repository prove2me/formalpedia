-- Prove2me | solution 2 for WeakGoldbach.even_goldbach_above_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T03:00:16.358602+00:00
-- url     : https://prove2.me/submissions/f8247e77-dc15-4b0a-893d-9f824d91889e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_prime_pair_above_2e18

theorem _root_.solution (n : ℕ) (h : 4 * 10 ^ 18 < n) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨r, hr⟩ := he
  have hr2 : 2 * 10 ^ 18 < r := by omega
  obtain ⟨t, hle, hp, hq⟩ := WeakGoldbach.symmetric_prime_pair_above_2e18 r hr2
  exact ⟨r - t, r + t, hp, hq, by omega⟩

#print axioms solution
