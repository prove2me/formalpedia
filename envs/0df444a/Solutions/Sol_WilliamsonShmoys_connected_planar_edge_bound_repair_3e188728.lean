-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_repair_3e188728
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:20.844019+00:00
-- url     : https://prove2.me/submissions/2147b564-dcaf-45ff-b5d2-63876da4c11a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hdraw : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
      H hdraw hconn hCard
  omega