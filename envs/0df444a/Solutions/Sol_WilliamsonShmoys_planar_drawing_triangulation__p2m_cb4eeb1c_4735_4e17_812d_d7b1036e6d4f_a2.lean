-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation__p2m_cb4eeb1c_4735_4e17_812d_d7b1036e6d4f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:56.546308+00:00
-- url     : https://prove2.me/submissions/c901163e-9040-4a8c-a013-954d201e14f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  rcases WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
      H hDraw hV with ⟨K, hSub, hKDraw, hCard, hMax⟩
  have hCount := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
    K hV hKDraw hMax
  exact ⟨K, hSub, hKDraw, hCard, hCount⟩