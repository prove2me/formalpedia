-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_lower_bound_from_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:12:22.921916+00:00
-- url     : https://prove2.me/submissions/0696e9c2-911d-4932-8fc6-44d40e61da73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_extendible

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  by_contra h
  have hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨K, hHK, hK, hnot⟩ :=
    WilliamsonShmoys.planar_sparse_graph_extendible H hV hH hsparse
  exact hnot (hMax K hHK hK)