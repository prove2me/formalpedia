-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:42:36.336726+00:00
-- url     : https://prove2.me/submissions/b4f9e420-513e-48c9-8c44-194d2ad9ccb2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1
    G hplanar hconn hcard
  omega