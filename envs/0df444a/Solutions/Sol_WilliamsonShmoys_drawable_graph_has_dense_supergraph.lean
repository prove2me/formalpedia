-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_dense_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:08:41.666245+00:00
-- url     : https://prove2.me/submissions/bd096490-43d5-4379-90fb-889d3e5df750

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ P : SimpleGraph V, M ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨P, hMP, hP, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e M hM
  exact ⟨P, hMP, hP,
    WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e P hV hP hmax⟩