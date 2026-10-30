-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_triangulation_edge_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:04:54.994102+00:00
-- url     : https://prove2.me/submissions/a1502a62-c73a-4de5-93ab-d3a20d96a96b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨L, hKL, hLdraw, hLmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph K hKdraw
  exact ⟨L, hKL, hLdraw,
    WilliamsonShmoys.edge_bound_of_maximal_drawable L hV hLdraw hLmax⟩