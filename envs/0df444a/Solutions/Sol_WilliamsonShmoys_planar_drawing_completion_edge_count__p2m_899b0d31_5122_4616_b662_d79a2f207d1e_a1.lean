-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_899b0d31_5122_4616_b662_d79a2f207d1e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:39.906824+00:00
-- url     : https://prove2.me/submissions/c3e829d4-110e-4c03-993d-96672913e80b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        3 * Fintype.card V = H.edgeFinset.card + 6) := by
  obtain ⟨H, hGH, hH, hmax⟩ := WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1 G hG hcard
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1 H hH hcard hmax