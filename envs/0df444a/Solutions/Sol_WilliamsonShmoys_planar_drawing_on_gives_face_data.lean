-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_gives_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:40:04.467081+00:00
-- url     : https://prove2.me/submissions/c44883ea-219a-41b4-b56e-3a5c50f6946a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_faces
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_for_face_data

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 ∧
      3 * F <= 2 * J.edgeSet.ncard := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_faces J hConn hJ
  refine ⟨F, hEuler, ?_⟩
  have hEdge :=
    WilliamsonShmoys.planar_simple_edge_bound_for_face_data J hConn hV hJ
  omega
