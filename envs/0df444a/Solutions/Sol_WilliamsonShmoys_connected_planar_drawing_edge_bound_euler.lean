-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:24:06.619863+00:00
-- url     : https://prove2.me/submissions/97c85ce9-4cd0-4898-ab11-d119796c4cea

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_euler_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : ∀ u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, i, hEuler, hFaceLength, hIncidences⟩ :=
    WilliamsonShmoys.planar_drawing_face_incidence_euler_data J hConn hV hJ
  omega