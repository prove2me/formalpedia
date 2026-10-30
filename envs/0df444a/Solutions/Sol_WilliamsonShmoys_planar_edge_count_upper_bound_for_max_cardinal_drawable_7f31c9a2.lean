-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:23:32.220354+00:00
-- url     : https://prove2.me/submissions/f5883c8c-08d7-4aeb-b081-34ba9f7565c1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_bound_7f31c9a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, _hContains, hCardinalities, _hDrawH, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_bound_7f31c9a2 K hDraw hCard
  omega