-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_planar_edge_count_euler_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:37:36.284987+00:00
-- url     : https://prove2.me/submissions/22b6279d-04c5-41d4-8e0b-db75ebd9261c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_has_triangulated_edge_count_certificate
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨m, f, hEdge, hEuler, hFaces⟩ :=
    WilliamsonShmoys.drawing_has_triangulated_edge_count_certificate G hG hCard
  omega