-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_extends_to_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:06:22.681993+00:00
-- url     : https://prove2.me/submissions/6b11525c-f1e0-4516-8eb4-0e954d1fb9f1

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
        R.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex Q hV hQdraw
