-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:07:46.395992+00:00
-- url     : https://prove2.me/submissions/619000a6-16a6-409a-9a36-e68c8ac6be4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_lower_edge_bound

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H →
        N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet))
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨H, hH, hNH, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_lower_edge_bound N hN.1 hV
  have hHN : H.edgeSet ⊆ N.edgeSet := hN.2 H hH hNH
  have hEq : H.edgeSet = N.edgeSet := Set.Subset.antisymm hHN hNH
  simpa [hEq] using hbound