-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:50:45.852049+00:00
-- url     : https://prove2.me/submissions/a34e8abc-e7b0-4c05-be07-9f721817ad49

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_count_data

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, b, hEuler, hBoundary, hIncidences⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_certificate K hKdraw hconn hCard
  exact WilliamsonShmoys.planar_edge_bound_from_face_count_data
    (Fintype.card V) K.edgeSet.ncard f b hEuler hBoundary hIncidences