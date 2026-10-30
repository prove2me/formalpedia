-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_with_maximal_edge_count_0319396f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:48:10.538031+00:00
-- url     : https://prove2.me/submissions/6f8cc34e-1dd3-4454-a389-a3e29d50d11c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_drawable_supergraph K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph
    L hL hV hmax