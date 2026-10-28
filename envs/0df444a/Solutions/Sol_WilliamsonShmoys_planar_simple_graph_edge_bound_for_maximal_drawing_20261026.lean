-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_for_maximal_drawing_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:58:11.227534+00:00
-- url     : https://prove2.me/submissions/53cf73d6-24a3-414d-bbeb-b745aba0d6f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_edge_monotone
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHconn, hHplanar, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_edge_monotone G hG
  have hBound := WilliamsonShmoys.connected_planar_drawing_edge_bound H hV hHconn hHplanar
  omega