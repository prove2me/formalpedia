-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_face_count_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:50:49.387346+00:00
-- url     : https://prove2.me/submissions/e62e159b-1513-427f-ab85-cea13589ef4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_from_crossing_free_arcs_eae47bd5
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_crossing_free_arcs_eae47bd5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.euler_from_crossing_free_arcs_eae47bd5 K hV hdraw hconn
  have hEdges : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.edge_bound_from_crossing_free_arcs_eae47bd5 K hV hdraw hconn
  refine ⟨f, hEuler, ?_⟩
  omega