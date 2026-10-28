-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:21:07.860357+00:00
-- url     : https://prove2.me/submissions/9e7eff35-72fa-42d9-8208-84519d235d32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_drawable_graph_completion_edge_count_of_maximal

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.drawable_graph_completion_edge_count_of_maximal H hH hCard hMax⟩
