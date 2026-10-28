-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:57:40.467662+00:00
-- url     : https://prove2.me/submissions/4d510bac-18db-4691-8925-e8b6ed9413fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_same_vertices_1bbd60bb_219d_439e_a299_3237c1a22baf
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_same_vertices_1bbd60bb_219d_439e_a299_3237c1a22baf K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_edge_count_1bbd60bb_219d_439e_a299_3237c1a22baf L hV hL hmax⟩