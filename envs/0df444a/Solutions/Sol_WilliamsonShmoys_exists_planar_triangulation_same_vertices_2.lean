-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_triangulation_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:23.278661+00:00
-- url     : https://prove2.me/submissions/fd98fd9e-6777-41f7-a4cb-3ba4ec6d43f4

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hV hH
