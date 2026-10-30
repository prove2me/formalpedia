-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:37:00.219533+00:00
-- url     : https://prove2.me/submissions/be0608a6-3d44-471b-8127-e4b0ce8eb6c5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_triangulation_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_edge_count
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal_for_triangulation_edge_count
      G hV hG
  refine ⟨L, hGL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_edge_count
    L hV hL hmax