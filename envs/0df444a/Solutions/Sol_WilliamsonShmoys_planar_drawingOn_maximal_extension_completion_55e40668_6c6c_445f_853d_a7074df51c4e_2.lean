-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:27:31.791287+00:00
-- url     : https://prove2.me/submissions/143b85f0-7078-4b16-be60-9de2ae307507

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by 
  classical
  obtain ⟨L, hMH, hmax⟩ := Set.Finite.exists_le_maximal
    (s := {K : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn K}) (Set.toFinite _) hK
  exact ⟨L, hMH, hmax.1, fun M hM hMp => le_antisymm (hmax.2 hMp hM) hM⟩
