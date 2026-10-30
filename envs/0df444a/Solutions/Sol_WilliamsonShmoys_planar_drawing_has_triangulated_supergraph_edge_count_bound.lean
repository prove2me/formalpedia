-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_edge_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:22:03.963588+00:00
-- url     : https://prove2.me/submissions/6cd245a2-ccfa-487b-bbe2-315d912bf3ad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph_for_triangulated_edge_count_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_for_triangulated_edge_count_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c G hG
  exact ⟨H, hGH,
    WilliamsonShmoys.edge_maximal_planar_graph_has_triangulated_edge_count_for_bound_2eec570b_ffd5_435e_a8fa_d87718384d1c H hH hMax hCard⟩