-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:37.247723+00:00
-- url     : https://prove2.me/submissions/45e25dda-da80-40cb-ba43-901e4af869cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_bound__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
import Theorems.Thm_WilliamsonShmoys_component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
    L hCard (by
      intro s hs hconn
      exact WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
        L hL s hs hconn)
