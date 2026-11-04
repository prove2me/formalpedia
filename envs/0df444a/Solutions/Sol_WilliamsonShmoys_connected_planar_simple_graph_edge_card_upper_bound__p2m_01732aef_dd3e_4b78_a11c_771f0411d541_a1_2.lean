-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T21:18:07.746484+00:00
-- url     : https://prove2.me/submissions/9ccd2a41-478f-4b7d-a648-425c182801a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have h := WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2 K hK hcard hconn
  omega