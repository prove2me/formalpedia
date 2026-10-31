-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:32.489786+00:00
-- url     : https://prove2.me/submissions/578d0495-eba5-4dd1-9cb4-69f4dbfbb837

import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 :=
  WilliamsonShmoys.connected_graph_edge_count_lower_bound G hconn
