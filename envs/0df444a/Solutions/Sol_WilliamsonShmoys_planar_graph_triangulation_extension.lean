-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:01:07.536186+00:00
-- url     : https://prove2.me/submissions/aa8da83f-41d9-4970-ad4d-369a17ac282a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_same_vertices_v2 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_edge_count_v2 H hH hmax hV⟩