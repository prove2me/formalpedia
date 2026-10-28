-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_can_be_augmented_to_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:00:05.941357+00:00
-- url     : https://prove2.me/submissions/a5aefa80-7d42-47eb-8a12-19987b0c423d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDrawing, hMax⟩ :=
    WilliamsonShmoys.planar_augmentation_finite_maximal_extension H hDrawing
  exact ⟨K, hHK, hKDrawing,
    WilliamsonShmoys.planar_augmentation_maximal_extension_edge_count K hKDrawing hMax hV⟩