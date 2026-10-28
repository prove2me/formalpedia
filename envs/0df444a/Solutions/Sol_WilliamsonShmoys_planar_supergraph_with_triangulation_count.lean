-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulation_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:04:13.239738+00:00
-- url     : https://prove2.me/submissions/4cf3f28c-e590-4856-9da2-2a8ce3477137
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_triangulation_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph G hG
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.maximal_planar_has_triangulation_edge_count L hV hL hmax⟩