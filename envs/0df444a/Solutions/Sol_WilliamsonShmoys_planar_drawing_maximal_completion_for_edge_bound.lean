-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_completion_for_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:21:56.126424+00:00
-- url     : https://prove2.me/submissions/74e5cdcf-6341-4375-ad07-e99f566f4eed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_maximal_extension_e9c82dc3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_from_arc_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hmax, hle⟩ :=
    WilliamsonShmoys.finite_drawable_supergraph_maximal_extension_e9c82dc3 M hM
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arc_drawing N hV hN hmax
  exact ⟨N, hMN, hN, hcount, hle⟩