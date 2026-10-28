-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_for_triangulation_extension_20261026
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:53:10.800075+00:00
-- url     : https://prove2.me/submissions/deb9fc8a-71a7-4f6b-bb40-88399848ff14

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | L ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨L, le_rfl, hL⟩
  exact ⟨H, hH.prop.1, hH.prop.2, fun K hK hPK =>
    le_antisymm (hH.2 ⟨le_trans hH.prop.1 hK, hPK⟩ hK) hK⟩
