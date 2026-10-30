-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_triangulation_extension_6e2fdad8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:47:16.332998+00:00
-- url     : https://prove2.me/submissions/d3582636-64fb-419b-8dbb-5362cd69d016

import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hHDrawing, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_completion_maximal_extension G hDrawing
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a
      H hHDrawing hMaximal hV
  exact ⟨H, hGH, hHDrawing, hCount⟩
