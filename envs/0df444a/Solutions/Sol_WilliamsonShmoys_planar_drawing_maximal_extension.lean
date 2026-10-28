-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:49:33.926084+00:00
-- url     : https://prove2.me/submissions/58aea030-338b-43f5-8df1-ea370214ebe8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by 
  classical
  obtain ⟨H, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hM
  exact ⟨H, hMH, hmax.1, fun K hK hKp => le_antisymm (hmax.2 hKp hK) hK⟩
