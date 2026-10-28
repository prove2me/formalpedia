-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulated_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:04:00.441357+00:00
-- url     : https://prove2.me/submissions/96468cff-6797-4b34-8ba0-be406771edf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_for_edgeCount_completion
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_for_edgeCount_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      (∀ u v, U.Adj u v → W.Adj u v) ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨W, hW⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edgeCount_completion U hU
  refine ⟨W, hW.1, hW.2.1, ?_⟩
  exact WilliamsonShmoys.planar_maximal_edge_count_for_edgeCount_completion W
    ⟨hW.1, (fun _ _ huv => huv), hW.2.2⟩ hCard