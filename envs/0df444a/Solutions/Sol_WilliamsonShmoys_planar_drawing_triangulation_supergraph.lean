-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:04:49.179788+00:00
-- url     : https://prove2.me/submissions/f23ad4e0-1558-4943-96d3-79b29a0d216e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hGT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph G hG
  refine ⟨T, hGT, hT, ?_⟩
  exact WilliamsonShmoys.planar_drawing_maximal_supergraph_edge_count T hV hT hmax
