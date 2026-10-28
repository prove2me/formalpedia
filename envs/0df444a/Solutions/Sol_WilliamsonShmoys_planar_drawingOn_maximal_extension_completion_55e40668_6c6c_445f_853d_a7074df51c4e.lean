-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:27:08.99813+00:00
-- url     : https://prove2.me/submissions/9f3b8b25-dbcd-4671-a7e7-6dea8de51d7d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  have hfin : ({J : SimpleGraph V | K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨K, le_rfl, hK⟩
  exact ⟨H, hH.prop.1, hH.prop.2, fun M hM hPM =>
    le_antisymm (hH.2 ⟨le_trans hH.prop.1 hM, hPM⟩ hM) hM⟩
