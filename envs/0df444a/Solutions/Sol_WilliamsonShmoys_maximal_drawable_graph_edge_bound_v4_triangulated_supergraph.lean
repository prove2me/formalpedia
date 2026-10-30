-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:04:27.411805+00:00
-- url     : https://prove2.me/submissions/1a80e267-c488-409a-b6e1-6eec40866181

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph_v4
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph_v4 M hdraw
  exact ⟨N, hMN, hNdraw,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_v4 N hNdraw hV hNmax⟩