-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:00.114923+00:00
-- url     : https://prove2.me/submissions/2409e5d4-17ab-415d-b33d-eea6ae781260
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
import Theorems.Thm_WilliamsonShmoys_euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card U - 6 := by
  obtain ⟨m', f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_certificate__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
      K hdraw
  exact WilliamsonShmoys.euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
    (Fintype.card U) K.edgeSet.ncard m' f hcard heuler