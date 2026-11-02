-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:46.152364+00:00
-- url     : https://prove2.me/submissions/eb655dbc-3953-4bfe-b39f-cf4640360ad5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hHK, hconn, hdrawK⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
      H (by omega) hdraw
  have hK :=
    WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
      K hcard hconn hdrawK
  have hEdges : H.edgeFinset.card ≤ K.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
  omega