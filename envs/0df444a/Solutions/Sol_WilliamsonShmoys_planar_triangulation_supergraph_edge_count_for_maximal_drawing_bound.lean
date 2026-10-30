-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count_for_maximal_drawing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:31:37.444484+00:00
-- url     : https://prove2.me/submissions/37075d6a-0b4c-49b4-8b85-fe9c2c376d81

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991 M hMdraw
  have hCount := WilliamsonShmoys.maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991 N hNdraw hNmax hCard
  exact ⟨N, hMN, hNdraw, hCount⟩