-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_maximal_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:37:24.141225+00:00
-- url     : https://prove2.me/submissions/7593e8d3-aec6-4ec6-9587-3913bb6b18ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_triangulation_extension_6e2fdad8

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ H : SimpleGraph V, K ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hHDrawing, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_completion_triangulation_extension_6e2fdad8
      K hDrawing hV
  have hHK : H = K := hMax H hKH hHDrawing
  rw [hHK] at hCount
  exact hCount.le