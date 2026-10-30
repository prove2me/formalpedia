-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_repair_053a8a16
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:54:50.361499+00:00
-- url     : https://prove2.me/submissions/447a2066-7aff-466a-921f-5b7d6463fa58

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ W : SimpleGraph V,
      G.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W →
      W.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨W, hGW, hWdraw, hWbound⟩ :=
    WilliamsonShmoys.planar_drawing_has_dense_extension G hV hG
  have hWG : W.edgeSet ⊆ G.edgeSet := hmax W hGW hWdraw
  have hcard : W.edgeSet.ncard ≤ G.edgeSet.ncard := Set.ncard_le_ncard hWG
  omega