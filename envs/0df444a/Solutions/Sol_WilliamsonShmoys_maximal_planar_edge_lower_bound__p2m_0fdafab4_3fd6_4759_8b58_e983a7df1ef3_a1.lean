-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:39:44.093666+00:00
-- url     : https://prove2.me/submissions/4a64fa85-d4e2-4c53-a74b-31ae4dd73a82

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  have hEq := maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1
    L hL hV hmax
  omega