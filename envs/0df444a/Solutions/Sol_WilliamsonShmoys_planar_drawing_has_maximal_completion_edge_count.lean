-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:09:23.693981+00:00
-- url     : https://prove2.me/submissions/31b8b7ce-1e7c-4523-b3ba-35002c377c35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_maximal_completion_50d04fde
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_50d04fde

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.finite_planar_drawing_maximal_completion_50d04fde H hDrawing hV
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_50d04fde K hK hV hMax⟩