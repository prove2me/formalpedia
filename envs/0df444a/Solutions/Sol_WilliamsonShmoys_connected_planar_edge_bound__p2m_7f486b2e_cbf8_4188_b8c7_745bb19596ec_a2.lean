-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:51:10.564198+00:00
-- url     : https://prove2.me/submissions/95e27413-0409-43e4-9943-cbc09083ecb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by
  by_cases hcard : 3 ≤ Fintype.card V
  · exact WilliamsonShmoys.connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
      G dG hG hconn hcard
  · exact WilliamsonShmoys.connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
      G dG hconn (Nat.lt_of_not_ge hcard)