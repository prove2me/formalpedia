-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_maximal_extension_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:06:33.904988+00:00
-- url     : https://prove2.me/submissions/60107d8f-3b39-446f-8af1-1cb1d31e737e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension K hDrawing hV
  have hLK : L = K := hMax L hKL hLDraw
  simpa [hLK] using hCount