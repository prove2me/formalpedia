-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:54:48.305827+00:00
-- url     : https://prove2.me/submissions/4c39d778-69f5-47e9-96d4-ace263042023

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ G : SimpleGraph V,
      M.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hMG, hGDraw, hGmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_extension
      M hV hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension
      G hV hGDraw hGmax
  exact ⟨G, hMG, hGDraw, hCount⟩
