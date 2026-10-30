-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:58:21.735013+00:00
-- url     : https://prove2.me/submissions/0f0c7e76-7883-4fbb-9e2e-ea854940a64e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : L.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
      L hL hV
  have hlower : 3 * Fintype.card V <= L.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
      L hL hV hmax
  omega