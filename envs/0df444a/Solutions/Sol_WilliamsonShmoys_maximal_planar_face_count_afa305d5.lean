-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_afa305d5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:11:26.282445+00:00
-- url     : https://prove2.me/submissions/6c041051-eaa0-413f-b388-6961241c8c02

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected_from_maximality_afa305d5
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_afa305d5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_afa305d5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    exists f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 /\
      2 * H.edgeSet.ncard = 3 * f := by
  have hConn : H.Connected :=
    WilliamsonShmoys.maximal_planar_drawing_connected_from_maximality_afa305d5
      H hDraw hCard hMax
  have hEulerExists :=
    WilliamsonShmoys.planar_drawing_euler_face_count_afa305d5
      H hDraw hConn
  have hEdge :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_afa305d5
      H hDraw hCard hMax
  cases hEulerExists with
  | intro f hEuler =>
      refine Exists.intro f (And.intro hEuler ?_)
      omega