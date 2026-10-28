-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_retry2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:29:42.059983+00:00
-- url     : https://prove2.me/submissions/cfae1261-820d-4c1f-9738-0756b6c77092
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_bound_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_retry2 G hDraw
  exact ⟨H, hGH, hHDraw,
    WilliamsonShmoys.maximal_drawable_planar_edge_bound_retry2 H hHDraw hMax hCard⟩
