-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:40:22.966721+00:00
-- url     : https://prove2.me/submissions/216a2e7a-efc2-4f94-83ba-e52a41e93e3f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hLT, hTDraw, hTMax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_supergraph
      L hDraw hCard
  have hCount :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count
      T hTDraw hCard hTMax
  exact ⟨T, hLT, hCount⟩