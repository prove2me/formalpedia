-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:34.772707+00:00
-- url     : https://prove2.me/submissions/9dbd67cc-39be-4696-a6f8-04317b6ce47b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1

set_option autoImplicit false

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
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  have hu := WilliamsonShmoys.planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1 H hH hV
  have hl := WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1 H hH hmax hV
  omega