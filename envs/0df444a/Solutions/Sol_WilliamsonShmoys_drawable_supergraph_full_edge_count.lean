-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_full_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:25:07.141838+00:00
-- url     : https://prove2.me/submissions/696834ae-0f98-421b-96e4-70a7bbb7c7bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_b5197173
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_full_edge_count_b5197173

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_b5197173 L hL
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_full_edge_count_b5197173 M hV hM hmax
  exact ⟨M, hLM, hM, hcount⟩