-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:31:54.600248+00:00
-- url     : https://prove2.me/submissions/08a4acc0-4d98-4a4e-bad4-7d004dec8d55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_augmentation_for_euler_bound_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count
set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound_maximal_extension G hG
  have hcount :=
    WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count H hV hH hmax
  exact ⟨H, hGH, hH, hcount⟩