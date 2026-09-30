-- Prove2me | solution 1 for WeakGoldbach.symmetric_prime_pair_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T22:48:55.57814+00:00
-- url     : https://prove2.me/submissions/2d685522-f149-419b-a1fe-457afd34789b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_pair_count_pos_above_2e18

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∃ t : ℕ, t ≤ m - 2 ∧ Nat.Prime (m - t) ∧ Nat.Prime (m + t) := by
  have hpos := WeakGoldbach.symmetric_pair_count_pos_above_2e18 m hm
  rw [Finset.card_pos] at hpos
  obtain ⟨t, ht⟩ := hpos
  rw [Finset.mem_filter] at ht
  obtain ⟨hrange, hpl, hpr⟩ := ht
  have := Finset.mem_range.mp hrange
  exact ⟨t, by omega, hpl, hpr⟩
