-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_same_vertex_count_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:41:28.390826+00:00
-- url     : https://prove2.me/submissions/e5fc971e-6090-4d01-9953-95c9ba719277
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_maximal_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_20261027

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.planar_extension_edge_maximal_20261027 G hDraw
  exact ⟨H, hGH, hHDraw,
    WilliamsonShmoys.maximal_planar_graph_edge_count_20261027 H hV hHDraw hMax⟩