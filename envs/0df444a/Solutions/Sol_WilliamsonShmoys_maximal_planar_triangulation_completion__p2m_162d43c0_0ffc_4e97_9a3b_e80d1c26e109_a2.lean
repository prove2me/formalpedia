-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:04:12.798199+00:00
-- url     : https://prove2.me/submissions/3dbe65d6-31f6-4639-aa63-68a08ff8334e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧
      HasPlanarDrawingOn R ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hDrawR, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
      Q hDraw
  exact ⟨R, hQR, hDrawR,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
      R hDrawR hV hmax⟩