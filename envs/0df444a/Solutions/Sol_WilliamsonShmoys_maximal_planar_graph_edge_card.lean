-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_card
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:52:22.361416+00:00
-- url     : https://prove2.me/submissions/2d2fb80f-c5d9-4d89-96aa-dd7418f5570a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_plane_map
import Theorems.Thm_WilliamsonShmoys_triangular_plane_map_edge_card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  exact WilliamsonShmoys.triangular_plane_map_edge_card L
    (WilliamsonShmoys.maximal_planar_drawing_has_triangular_plane_map
      L hL hMax hCard)