-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_three_n_minus_six_edges_target
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:13:32.540123+00:00
-- url     : https://prove2.me/submissions/58d6801a-8271-482b-a899-b15dbeeb0267
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hMDraw, hCount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulation_completion L hV hDraw
  have hML : M.edgeSet ⊆ L.edgeSet := hMax M hLM hMDraw
  have hEdges : L.edgeSet = M.edgeSet := Set.Subset.antisymm hLM hML
  rw [hEdges]
  exact hCount