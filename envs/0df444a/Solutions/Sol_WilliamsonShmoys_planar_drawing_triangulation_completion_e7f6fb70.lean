-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_e7f6fb70
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:27:44.339117+00:00
-- url     : https://prove2.me/submissions/bbc6f672-1620-41d9-a3d7-abbc68643686
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exists_e7f6fb70
import Theorems.Thm_WilliamsonShmoys_completion_maximal_edge_count_e7f6fb70

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, Y.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hsub, hle, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_completion_exists_e7f6fb70 Y hY
  have hcount :=
    WilliamsonShmoys.completion_maximal_edge_count_e7f6fb70 H hV hH hmax
  exact ⟨H, hsub, hH, hle, hcount⟩