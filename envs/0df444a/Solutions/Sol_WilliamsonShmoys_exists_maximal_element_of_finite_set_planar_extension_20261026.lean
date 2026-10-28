-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_element_of_finite_set_planar_extension_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:05:31.960668+00:00
-- url     : https://prove2.me/submissions/49dc9fc5-295e-48e0-9a83-e632b633ef9f

import Mathlib

theorem solution {α : Type} [PartialOrder α] [Finite α] (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, a ≤ b → b ∈ S → b = a := by
  obtain ⟨a, ha, hmax⟩ := S.toFinite.exists_maximal hS
  refine ⟨a, ha, fun b hab hb => ?_⟩
  exact le_antisymm (hmax hb hab) hab