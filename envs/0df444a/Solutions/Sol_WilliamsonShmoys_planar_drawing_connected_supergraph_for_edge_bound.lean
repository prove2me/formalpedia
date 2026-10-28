-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:19:46.994694+00:00
-- url     : https://prove2.me/submissions/07bff129-187d-42a8-89b3-62fe634d44ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawable_graph_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Q.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hQH, hHdraw, hEdgeCount, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_maximal Q hQdraw
  have hConnected :=
    WilliamsonShmoys.maximal_planar_drawable_graph_connected H hHdraw hMaximal hCard
  exact ⟨H, hConnected, hHdraw, hEdgeCount⟩