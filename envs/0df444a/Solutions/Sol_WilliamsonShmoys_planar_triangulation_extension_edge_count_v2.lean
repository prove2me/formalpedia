-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:31:58.896492+00:00
-- url     : https://prove2.me/submissions/a6ba8d68-e4e0-476c-8a73-9b4d0b9530b3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph_for_edge_count_v2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M <= N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_for_edge_count_v2 M hV hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count_v2 N hV hN hmax