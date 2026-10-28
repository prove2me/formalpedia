-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_planar_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:37:48.047008+00:00
-- url     : https://prove2.me/submissions/6528b015-65c1-4070-8f15-023af715600f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_connected_supergraph_for_edge_bound_3daf7e3a
import Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound_3daf7e3a
import Theorems.Thm_WilliamsonShmoys_drawable_edgeSet_ncard_mono_3daf7e3a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Q, hPQ, hQconn, hQdraw⟩ :=
    WilliamsonShmoys.drawable_connected_supergraph_for_edge_bound_3daf7e3a P hPdraw hCard
  have hQbound :=
    WilliamsonShmoys.connected_drawable_edge_bound_3daf7e3a Q hQdraw hQconn hCard
  have hEdges := WilliamsonShmoys.drawable_edgeSet_ncard_mono_3daf7e3a P Q hPQ
  omega