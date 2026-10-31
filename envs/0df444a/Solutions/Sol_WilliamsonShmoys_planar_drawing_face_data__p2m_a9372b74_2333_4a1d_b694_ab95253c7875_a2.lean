-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:30:04.28372+00:00
-- url     : https://prove2.me/submissions/646f9a36-5110-457e-bccd-1cb3d28db345

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
import Theorems.Thm_WilliamsonShmoys_finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    Nonempty (WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K) := by
  exact WilliamsonShmoys.finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2 K hV
    (WilliamsonShmoys.connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2 K hK hconn hV).1
    (WilliamsonShmoys.connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2 K hK hconn hV).2