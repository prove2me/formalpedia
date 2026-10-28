-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:05:43.68599+00:00
-- url     : https://prove2.me/submissions/0a1a0f2d-b55c-4118-b6c7-bd35be807ae8

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V), K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  exact ⟨H, hGH, hmax.1, fun L hHL hL => le_antisymm (hmax.2 hL hHL) hHL⟩
