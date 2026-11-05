-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:00.347883+00:00
-- url     : https://prove2.me/submissions/c44503ca-f873-435f-847a-0a2aa60afcd2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          G ≤ H ∧
          H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK hstep