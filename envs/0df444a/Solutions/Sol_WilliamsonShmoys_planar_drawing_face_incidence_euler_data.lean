-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_incidence_euler_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:47:51.974181+00:00
-- url     : https://prove2.me/submissions/626c1b9b-9354-4822-9bf2-5ea818ce95a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_for_face_data
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_face_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    exists f i : Nat,
      Fintype.card V + f = J.edgeSet.ncard + 2 /\
      3 * f <= i /\
      i = 2 * J.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula_for_face_data J hConn hJ
  have hBound :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_data J hConn hV hJ
  refine ⟨f, 2 * J.edgeSet.ncard, hEuler, ?_, rfl⟩
  omega