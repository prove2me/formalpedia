-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_completion_edge_count_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:51:25.098978+00:00
-- url     : https://prove2.me/submissions/2903b8fe-e65a-42bb-bc30-7f04a31d79bc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_exists
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ T : SimpleGraph V, Z ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨T, hZT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists Z hZ
  exact ⟨T, hZT, hT,
    WilliamsonShmoys.planar_drawingOn_maximal_edge_count T hV hT hmax⟩