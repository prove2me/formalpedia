-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:59:28.59647+00:00
-- url     : https://prove2.me/submissions/61d299b0-fc55-4bdd-8ee4-1c2d1dbd4346

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_extension_same_vertex_type
import Theorems.Thm_WilliamsonShmoys_maximal_simple_planar_supergraph_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_maximal_extension_same_vertex_type M hM hV
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_simple_planar_supergraph_triangulation_edge_count N hN hV hMax