-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:37:48.74539+00:00
-- url     : https://prove2.me/submissions/335050cb-f42b-4018-9a07-d6a536adf0f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_b426a2d2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound_b426a2d2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by
  obtain ⟨U, hGU, hU, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_b426a2d2 G hG
  exact ⟨U, hGU, hU,
    WilliamsonShmoys.maximal_planar_graph_edge_bound_b426a2d2 U hV hU hmax⟩