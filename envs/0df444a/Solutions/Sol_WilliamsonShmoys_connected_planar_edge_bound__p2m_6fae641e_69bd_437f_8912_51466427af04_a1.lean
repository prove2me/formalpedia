-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:02:21.623886+00:00
-- url     : https://prove2.me/submissions/d7fac22f-56d7-43b5-b75f-0b972b44fa77

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1 G hconn hG
  have hFaces := WilliamsonShmoys.connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1 G hV hconn hG f hEuler
  omega