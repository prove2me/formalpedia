-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_for_edgeCount_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:16:28.921956+00:00
-- url     : https://prove2.me/submissions/18683f05-7b5f-4ced-bf94-1ea1542a3ed1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulation_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion W W)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  rcases WilliamsonShmoys.planar_drawing_edge_count_triangulation_completion
      W hW.1 hCard with ⟨X, hX, hWX, hCount⟩
  have hEq : X = W := hW.2.2 X hX hWX
  rw [← hEq]
  exact hCount