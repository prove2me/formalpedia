-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:39:35.103059+00:00
-- url     : https://prove2.me/submissions/e11896e7-f272-4aa0-9a55-81d8af5fe7b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_edge_completion_finite_max
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_euler

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      (∀ u v, W.Adj u v → X.Adj u v) ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨X, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_edge_completion_finite_max W hW
  rcases hmax with ⟨hX, hWX, hmaximal⟩
  refine ⟨X, hX, hWX, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler
    W X ⟨hX, hWX, hmaximal⟩ hCard