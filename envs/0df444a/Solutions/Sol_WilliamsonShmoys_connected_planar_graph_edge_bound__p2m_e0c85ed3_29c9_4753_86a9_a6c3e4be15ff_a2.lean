-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:55:53.5642+00:00
-- url     : https://prove2.me/submissions/983c7599-2f6c-428c-b06f-0844f091aa90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hsub, _hHdraw, hHcard⟩ :=
    WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
      G hcard hconn hdraw
  have h_edges : G.edgeFinset.card ≤ H.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
  omega