-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:42:20.165075+00:00
-- url     : https://prove2.me/submissions/785cb43f-8b67-42bf-a37e-27f146c22d6b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {α : Type} [PartialOrder α]
    (s : Set α) (hne : s.Nonempty) (hfin : s.Finite) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  obtain ⟨a, ha, hmax⟩ := hfin.exists_maximal hne
  exact ⟨a, ha, fun b hb hab => hmax hb hab⟩
