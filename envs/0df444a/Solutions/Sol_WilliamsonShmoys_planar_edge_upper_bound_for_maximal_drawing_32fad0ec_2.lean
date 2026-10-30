-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_32fad0ec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:47:27.053529+00:00
-- url     : https://prove2.me/submissions/753442dc-a7a5-4245-a64d-e1ca9c343796

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
  | (apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55 <;> assumption)
