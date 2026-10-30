-- Prove2me | solution 1 for WilliamsonShmoys.connected_supergraph_of_disconnected_planar__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:31:25.059338+00:00
-- url     : https://prove2.me/submissions/223d0209-fd43-4d58-89d0-37ca4e696e2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
import Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard + 1 ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hHconn, hHplan⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
      G hG hV hdis
  have hcard :=
    WilliamsonShmoys.strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
      G H hGH hHconn hdis
  exact ⟨H, hGH, hHconn, hHplan, hcard⟩