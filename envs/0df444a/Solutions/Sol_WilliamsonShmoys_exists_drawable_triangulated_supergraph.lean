-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_triangulated_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:15:41.287793+00:00
-- url     : https://prove2.me/submissions/776ac4a6-0f3c-4954-a43b-1e54566bd5cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_maximizing_edges
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_from_arc_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_maximizing_edges L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_edge_count_from_arc_drawing M hV hM hmax