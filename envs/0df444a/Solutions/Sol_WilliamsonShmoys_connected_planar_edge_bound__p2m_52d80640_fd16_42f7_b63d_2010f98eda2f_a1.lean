-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:28:00.870392+00:00
-- url     : https://prove2.me/submissions/25c7c838-2544-44cb-beaa-369065e23ed9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
import Theorems.Thm_WilliamsonShmoys_planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨f, heuler, hboundary⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
      K hV hconn hK
  exact WilliamsonShmoys.planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
    (Fintype.card V) K.edgeFinset.card f hV heuler hboundary