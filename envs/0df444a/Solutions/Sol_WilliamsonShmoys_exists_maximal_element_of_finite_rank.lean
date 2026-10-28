-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_element_of_finite_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:20.942209+00:00
-- url     : https://prove2.me/submissions/6d9fafa4-5ebc-4a98-b42b-17f0fd525ef8

import Mathlib


theorem solution {α : Type} [Fintype α] (P : α → Prop) (R : α → α → Prop) (rank : α → Nat) (hP : ∃ x, P x) (hRank : ∀ x y, P x → P y → R x y → x ≠ y → rank x < rank y) : ∃ x, P x ∧ ∀ y, P y → R x y → y = x := by
  classical
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) rank
    ⟨x0, by simp [hx0]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hmax
  refine ⟨x, hx, fun y hy hR => ?_⟩
  by_contra hne
  have h1 := hRank x y hx hy hR (Ne.symm hne)
  have h2 := hmax y hy
  omega
