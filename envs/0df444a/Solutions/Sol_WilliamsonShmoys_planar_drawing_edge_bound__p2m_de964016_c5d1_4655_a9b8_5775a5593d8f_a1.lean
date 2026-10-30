-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_de964016_c5d1_4655_a9b8_5775a5593d8f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:00.246969+00:00
-- url     : https://prove2.me/submissions/0b5489bc-4957-4c11-9c4f-02f94ae58aaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, _hsub, _hDrawK, hCardMonotone, hTriangulatedCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2
      H hDraw hV
  omega