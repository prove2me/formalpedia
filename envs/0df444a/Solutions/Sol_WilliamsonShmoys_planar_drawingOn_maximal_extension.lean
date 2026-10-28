-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:48:37.975322+00:00
-- url     : https://prove2.me/submissions/6db62c05-fa62-45ee-baea-c410fc0d8c82

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V), G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by 
  classical
  obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal (p := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K) hG
  exact ⟨H, hGH, hmax.1, fun K hHK hK => hmax.2 hK hHK⟩
