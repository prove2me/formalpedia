-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulating_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:37:59.50128+00:00
-- url     : https://prove2.me/submissions/7041096b-b215-4ec3-8dbe-b40f7b2a16bc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph_399d67b6_1225_43ef_9a0c_578821b9bf96
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_399d67b6_1225_43ef_9a0c_578821b9bf96 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96 L hL hMax hCard⟩