-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_step_of_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:30:53.11847+00:00
-- url     : https://prove2.me/submissions/836ce4d0-6f42-4937-8e2d-9ebba687c8a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_step_of_three_vertices_exists_unreachable_pair
import Theorems.Thm_WilliamsonShmoys_connected_step_of_three_vertices_add_planar_edge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by
  obtain ⟨u, v, hUnreachable⟩ :=
    WilliamsonShmoys.connected_step_of_three_vertices_exists_unreachable_pair G hCard hDisconnected
  obtain ⟨H, hSubgraph, hDrawing, hAddedEdge⟩ :=
    WilliamsonShmoys.connected_step_of_three_vertices_add_planar_edge G hG u v hUnreachable
  exact ⟨H, hSubgraph, hDrawing, u, v, hUnreachable, hAddedEdge⟩