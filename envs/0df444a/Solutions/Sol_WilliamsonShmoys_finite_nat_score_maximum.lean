-- Prove2me | solution 1 for WilliamsonShmoys.finite_nat_score_maximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:17:52.872756+00:00
-- url     : https://prove2.me/submissions/27114fad-bf43-416a-99c5-e0011ab03501

import Mathlib
set_option autoImplicit false
theorem solution
    {α : Type} [Fintype α]
    (P : α → Prop) (score : α → Nat) (x : α) (hx : P x) :
    ∃ y : α, P y ∧ score x ≤ score y ∧ ∀ z : α, P z → score z ≤ score y := by
  classical
  obtain ⟨y, hy, hmax⟩ := (Finset.univ.filter P).exists_max_image score
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  exact ⟨y, (Finset.mem_filter.mp hy).2, hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩),
    fun z hz => hmax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)⟩
