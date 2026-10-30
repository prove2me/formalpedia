-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_can_add_edge_below_maximum_v4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:35:14.316005+00:00
-- url     : https://prove2.me/submissions/d147ca9e-0ff2-4636-bf5a-ff29e151732f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph_v4
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_v4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hBelow : (L.edgeSet.ncard : Int) <
      3 * (Fintype.card V : Int) - 6) :
    ∃ M : SimpleGraph V, L < M ∧ HasPlanarDrawingOn M := by
  obtain ⟨M, hLM, hdrawM, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_v4 L hdraw
  have hcard := WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4 M hdrawM hV hmax
  have hne : L ≠ M := by
    intro heq
    have hcounts : (L.edgeSet.ncard : Int) = (M.edgeSet.ncard : Int) := by
      rw [heq]
    omega
  exact ⟨M, lt_of_le_of_ne hLM hne, hdrawM⟩