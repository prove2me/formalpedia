-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:33.062732+00:00
-- url     : https://prove2.me/submissions/171d714d-6472-4c33-bae4-21ded16ce884
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hConn : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hboundary⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
      H hConn hDraw hV
  exact WilliamsonShmoys.edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
    H hV ⟨f, heuler, hboundary⟩