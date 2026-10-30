-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:47:54.435807+00:00
-- url     : https://prove2.me/submissions/fc4fba18-22f6-4876-b63e-7c40e7b8625e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_24bcd821_2a94_4cb2_b06f_eb5106ed464b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_24bcd821_2a94_4cb2_b06f_eb5106ed464b L hL hV
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_24bcd821_2a94_4cb2_b06f_eb5106ed464b M hM hV hMax