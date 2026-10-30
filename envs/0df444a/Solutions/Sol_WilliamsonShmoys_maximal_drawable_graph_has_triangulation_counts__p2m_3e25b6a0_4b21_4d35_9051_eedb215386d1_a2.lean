-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_counts__p2m_3e25b6a0_4b21_4d35_9051_eedb215386d1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:56.771947+00:00
-- url     : https://prove2.me/submissions/18f95065-663f-438d-ad41-a67de93cdb8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      2 * H.edgeSet.ncard = 3 * f /\
      Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hE := WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4 H hH hmax hV
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega