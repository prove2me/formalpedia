-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:32.768994+00:00
-- url     : https://prove2.me/submissions/94a80d0f-4dfd-42b8-80d2-6f3ec5cc45a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    X.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2 X hX hV
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2 X hX hV hmax
  omega