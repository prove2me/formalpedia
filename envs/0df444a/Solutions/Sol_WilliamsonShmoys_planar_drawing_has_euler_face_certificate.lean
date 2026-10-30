-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_euler_face_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:47:47.969444+00:00
-- url     : https://prove2.me/submissions/c1129a9f-a3e9-4864-a7f3-7656d2b8b102

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_faces
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      (Fintype.card V : Int) - (H.edgeSet.ncard : Int) + (f : Int) = 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count H hconn hH
  refine ⟨f, heuler, ?_⟩
  have hedge :=
    WilliamsonShmoys.planar_drawing_edge_bound_from_faces H hV hconn hH
  omega