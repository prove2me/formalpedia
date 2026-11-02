-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound__p2m_26fdce0d_6688_44e7_929e_c61ea3cc0bd1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:07.778105+00:00
-- url     : https://prove2.me/submissions/a217d9fd-8a05-4671-8904-ef69c9314292
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_connected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  by_cases hconn : H.Connected
  · exact WilliamsonShmoys.planar_graph_edge_bound_connected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
      H hcard hconn hdraw
  · exact WilliamsonShmoys.planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
      H hcard hconn hdraw