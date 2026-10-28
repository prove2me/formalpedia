-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_395ae7cf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:39:00.252708+00:00
-- url     : https://prove2.me/submissions/cc019208-acbb-402b-93ea-7891fd2ab16e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_395ae7cf
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_395ae7cf

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hG, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_395ae7cf H hH
  refine ⟨G, hHG, hG, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_graph_edge_count_395ae7cf G hV hG hmax