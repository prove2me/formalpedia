-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:36:25.395813+00:00
-- url     : https://prove2.me/submissions/048323f2-652d-48bf-a67b-564f07194a3f

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40
import Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_edge_maximal_planar_on_c5621e40

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHDrawing, hEdgeCount, hMaximal⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40 G hDrawing
  exact ⟨H, hGH, hHDrawing, hEdgeCount,
    WilliamsonShmoys.edge_count_eq_of_edge_maximal_planar_on_c5621e40 H hHDrawing hV hMaximal⟩