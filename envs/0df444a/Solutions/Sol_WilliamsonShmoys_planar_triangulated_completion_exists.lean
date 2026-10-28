-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_completion_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:38:36.311564+00:00
-- url     : https://prove2.me/submissions/2a00b5d1-7dd2-42e2-b5c5-136e10a89675
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximizing_edges
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmaxL⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximizing_edges L hL
  refine ⟨M, hLM, hM, ?_⟩
  apply WilliamsonShmoys.edge_count_of_edge_maximal_planar M hM hV
  intro N hMN hN
  exact hmaxL N (le_trans hLM hMN) hN