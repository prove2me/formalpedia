-- Prove2me | solution 1 for WilliamsonShmoys.ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:33:50.07199+00:00
-- url     : https://prove2.me/submissions/15bbdb5b-695b-47f0-88a7-aad117d19b61

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α]
    (s t : Set α) (k : ℕ)
    (hsub : s ⊆ t)
    (hcard : t.ncard = k) :
    s.ncard ≤ k := by
  calc
    s.ncard ≤ t.ncard := Set.ncard_le_ncard hsub
    _ = k := hcard