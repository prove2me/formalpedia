-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:28.66412+00:00
-- url     : https://prove2.me/submissions/8c1fe792-465d-49a4-9298-d948f5325e4c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  exact WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
    H hDraw hV