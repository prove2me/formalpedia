-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_edge_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:32:32.117883+00:00
-- url     : https://prove2.me/submissions/369a311e-5c37-4500-b4e0-bc22fcde0c5f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_ncard
import Theorems.Thm_WilliamsonShmoys_graph_le_of_le_of_edge_ncard_le

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  obtain ⟨M, hLM, hMdraw, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_max_ncard L hLdraw
  refine ⟨M, hLM, hMdraw, ?_⟩
  intro N hMN hNdraw
  apply WilliamsonShmoys.graph_le_of_le_of_edge_ncard_le M N hMN
  exact hmax N (le_trans hLM hMN) hNdraw