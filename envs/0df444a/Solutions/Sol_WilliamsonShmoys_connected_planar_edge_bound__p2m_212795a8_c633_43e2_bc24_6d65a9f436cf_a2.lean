-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:52:32.602151+00:00
-- url     : https://prove2.me/submissions/26eb1143-0faa-4500-8e12-ed428f634436
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨D⟩ := WilliamsonShmoys.planar_drawing_face_data__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K hK hconn hV
  exact WilliamsonShmoys.euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K D hV