-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_graph_edge_bound_from_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:06:55.938451+00:00
-- url     : https://prove2.me/submissions/717405ec-03b5-4cd2-9e6d-40897b2f0625
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion_for_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨N, _hMN, _hN, hCard, hle⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_completion_for_edge_bound M hV hM
  rw [← hCard]
  exact hle