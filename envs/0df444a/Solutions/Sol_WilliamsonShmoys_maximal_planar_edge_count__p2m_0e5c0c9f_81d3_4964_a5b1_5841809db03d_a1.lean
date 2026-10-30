-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:11.140788+00:00
-- url     : https://prove2.me/submissions/fd6add87-88a4-4224-bfe4-e778bb79d1a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H)
    (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1 H hDraw hMax hV
  have hhi := WilliamsonShmoys.planar_edge_upper_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1 H hDraw hV
  omega