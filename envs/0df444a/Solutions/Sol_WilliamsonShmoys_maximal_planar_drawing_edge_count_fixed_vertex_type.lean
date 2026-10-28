-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_fixed_vertex_type
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:02:32.605556+00:00
-- url     : https://prove2.me/submissions/39a1a886-6ff6-4557-8582-2d13955b36e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e H hH hV
  have hLower := WilliamsonShmoys.maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e H hH hV hmax
  omega