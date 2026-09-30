-- Prove2me | solution 2 for WeakGoldbach.symmetric_prime_pair_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T02:59:01.049209+00:00
-- url     : https://prove2.me/submissions/26e5b321-b485-42a7-8350-dc6c64064b4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_pair_count_pos_above_2e18

theorem _root_.solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∃ t : ℕ, t ≤ m - 2 ∧ Nat.Prime (m - t) ∧ Nat.Prime (m + t) := by
  have hcard := WeakGoldbach.symmetric_pair_count_pos_above_2e18 m hm
  obtain ⟨t, ht⟩ := Finset.card_pos.1 hcard
  rw [Finset.mem_filter, Finset.mem_range] at ht
  exact ⟨t, by omega, ht.2.1, ht.2.2⟩

#print axioms solution
