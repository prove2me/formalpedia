-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:56.934986+00:00
-- url     : https://prove2.me/submissions/6bc1b8b9-24ce-4991-8cc3-f8d7b57d7034
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    Fintype.card V <= K.edgeSet.ncard + 1 /\
      K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  exact
    ⟨WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
        K hconn,
      WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
        K hK hV⟩