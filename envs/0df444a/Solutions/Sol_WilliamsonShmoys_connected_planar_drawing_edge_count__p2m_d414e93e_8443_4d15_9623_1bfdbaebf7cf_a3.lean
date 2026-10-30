-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:49.760856+00:00
-- url     : https://prove2.me/submissions/50212c3c-67ba-4731-a5bf-6e93ab802338
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
import Theorems.Thm_WilliamsonShmoys_euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, hF, hEuler, hInc⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
      M hM hconn hV
  exact WilliamsonShmoys.euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
    M F hEuler hInc