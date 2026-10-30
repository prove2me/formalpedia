-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_card_of_predicate__p2m_8f4450fd_25bb_4306_b9c5_7a9c9b261a7b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:10.229397+00:00
-- url     : https://prove2.me/submissions/2a2e9b3d-3169-4f53-88c1-cdba843d609b

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hex with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  apply hmax b
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩