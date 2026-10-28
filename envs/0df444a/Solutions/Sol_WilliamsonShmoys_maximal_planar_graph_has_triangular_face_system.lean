-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_triangular_face_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:31:45.724949+00:00
-- url     : https://prove2.me/submissions/f21618f5-adcd-4ff2-9ca2-8a89a60d9e53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_graph_sharp_edge_count_has_triangular_face_system
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_sharp_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H <= K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by
  have hedge : H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_graph_has_sharp_edge_count H hV hH hmax
  exact WilliamsonShmoys.planar_graph_sharp_edge_count_has_triangular_face_system
    H hV hH hedge