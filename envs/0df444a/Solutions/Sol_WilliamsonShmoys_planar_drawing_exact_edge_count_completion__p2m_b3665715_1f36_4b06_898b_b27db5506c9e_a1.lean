-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:40.843616+00:00
-- url     : https://prove2.me/submissions/4f19d977-866c-4692-8564-501353e0879d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
      G hG hV
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
    K hK hV hmax