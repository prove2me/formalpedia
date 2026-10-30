-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:34:18.828011+00:00
-- url     : https://prove2.me/submissions/648ce329-a84a-4713-8f57-71191c069603
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hMax : forall H : SimpleGraph V,
      Set.Subset T.edgeSet H.edgeSet ->
      HasPlanarDrawingOn H ->
      Set.Subset H.edgeSet T.edgeSet)
    (hV : 3 <= Fintype.card V) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3 T hT hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3 T hT hMax hV
  omega