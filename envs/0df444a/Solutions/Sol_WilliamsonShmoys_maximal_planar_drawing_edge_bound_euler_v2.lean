-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_euler_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:03:59.311495+00:00
-- url     : https://prove2.me/submissions/7a9a19ee-d0fb-4741-a2fb-71c6bfa7f069
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_face_system
import Theorems.Thm_WilliamsonShmoys_triangular_face_system_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall H' : SimpleGraph V, H < H' ->
      ¬ (WilliamsonShmoys.HasPlanarDrawingOn H')) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hfaces : WilliamsonShmoys.HasTriangularPlaneFaceSystem H :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangular_face_system
      H hV hconn hH hmax
  exact WilliamsonShmoys.triangular_face_system_edge_bound H hfaces