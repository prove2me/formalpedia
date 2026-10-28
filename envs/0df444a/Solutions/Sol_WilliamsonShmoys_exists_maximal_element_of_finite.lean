-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_element_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:55:46.532944+00:00
-- url     : https://prove2.me/submissions/67ecc038-04aa-4364-9a78-a91b063e2443

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [PartialOrder α] [Finite α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by
  obtain ⟨a, ha⟩ := S.toFinite.exists_maximal hS
  exact ⟨a, ha.1, ha.2⟩