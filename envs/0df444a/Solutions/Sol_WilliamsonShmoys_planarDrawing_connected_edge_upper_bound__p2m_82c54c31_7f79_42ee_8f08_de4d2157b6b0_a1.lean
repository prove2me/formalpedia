-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:19:10.716287+00:00
-- url     : https://prove2.me/submissions/8b088964-f99a-41ce-8ecd-840f7ffcccfd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hCount :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2
      K hK hconn hV
  cases hCount with
  | intro f hf =>
    cases hf with
    | intro hEuler hFaces => omega