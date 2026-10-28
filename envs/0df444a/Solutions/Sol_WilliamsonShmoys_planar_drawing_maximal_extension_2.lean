-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:50:31.469594+00:00
-- url     : https://prove2.me/submissions/855ee77b-47dd-4206-a43f-e46219ed11b7

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
  have hfin : ({J : SimpleGraph V | M ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨M, le_rfl, hM⟩
  exact ⟨H, hH.prop.1, hH.prop.2, fun K hK hPK =>
    le_antisymm (hH.2 ⟨le_trans hH.prop.1 hK, hPK⟩ hK) hK⟩
