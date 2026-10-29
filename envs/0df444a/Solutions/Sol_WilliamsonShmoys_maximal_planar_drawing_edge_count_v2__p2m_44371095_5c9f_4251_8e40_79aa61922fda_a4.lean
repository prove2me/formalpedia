-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:40:38.768195+00:00
-- url     : https://prove2.me/submissions/3b94264b-9b9c-46a6-bb0e-85a6dd1d6884
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1 H hDraw hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1 H hDraw hV hMax
  omega