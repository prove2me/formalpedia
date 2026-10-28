-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:55:56.929087+00:00
-- url     : https://prove2.me/submissions/13fa20e1-c9ea-4a75-9e71-749212a10647

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  have hfin : ({J : SimpleGraph V | L ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨L, le_rfl, hL⟩
  exact ⟨H, hH.prop.1, hH.prop.2, fun K hK hPK => hH.2 ⟨le_trans hH.prop.1 hK, hPK⟩ hK,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hH.prop.1) (Set.toFinite _)⟩
