-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_incidence_bound_edge_bound_fd674c06_a657_4ca8_b75f_41f75c897817
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:09:14.604583+00:00
-- url     : https://prove2.me/submissions/a5b9d00f-bf64-4b96-b18b-0402d497e7ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_euler_inequalities

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hBoundary⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_euler_inequalities
      K hconn hdraw hV
  omega