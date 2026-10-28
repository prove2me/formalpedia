-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_completion_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:58:34.514995+00:00
-- url     : https://prove2.me/submissions/4a3b3174-c4ec-4dd0-9c87-4ca2b72654e2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simpleGraph_supergraph_maximal
import Theorems.Thm_simpleGraph_edgeSet_ncard_mono

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (∀ K : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H) ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    finite_simpleGraph_supergraph_maximal
      WilliamsonShmoys.HasPlanarDrawingOn G hDrawing
  exact ⟨H, hGH, hH, hMax, simpleGraph_edgeSet_ncard_mono G H hGH⟩