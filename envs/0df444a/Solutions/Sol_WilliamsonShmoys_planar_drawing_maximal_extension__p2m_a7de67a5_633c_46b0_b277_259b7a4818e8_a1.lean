-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:29:08.083339+00:00
-- url     : https://prove2.me/submissions/c7c58e80-dcd1-4a3e-9d30-f2ceb4f29166

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) := by
  classical
  let q : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hq : q K := ⟨le_rfl, hK⟩
  obtain ⟨L, hKL, hmax⟩ := Finite.exists_le_maximal (p := q) hq
  refine ⟨L, hKL, hmax.1.2, ?_⟩
  intro M hLM hM
  have hqM : q M := ⟨hKL.trans hLM, hM⟩
  have hML : M ≤ L := hmax.2 hqM hLM
  exact (le_antisymm hLM hML).symm