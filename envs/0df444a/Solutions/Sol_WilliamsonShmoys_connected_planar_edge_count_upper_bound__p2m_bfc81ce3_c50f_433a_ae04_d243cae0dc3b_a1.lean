-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:28.207303+00:00
-- url     : https://prove2.me/submissions/93a8df5a-28eb-48c9-9fa4-eb6456bbb74f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_degree_sum__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
      T hV hT hconn
  have hFaces :=
    WilliamsonShmoys.planar_drawing_face_degree_sum__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
      T hV hT hconn f hEuler
  omega