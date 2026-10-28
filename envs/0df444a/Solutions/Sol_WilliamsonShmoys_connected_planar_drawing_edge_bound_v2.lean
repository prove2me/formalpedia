-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:55:24.81716+00:00
-- url     : https://prove2.me/submissions/3ed1e423-143c-4b9b-9f6f-2bdb3dbb8705
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_counting
import Theorems.Thm_WilliamsonShmoys_euler_face_counting_edge_bound

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.euler_face_counting_edge_bound K
    (WilliamsonShmoys.planar_drawing_euler_face_counting K hV hconn hK)