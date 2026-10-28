-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_completion_for_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:59:59.431455+00:00
-- url     : https://prove2.me/submissions/a31bb6a8-7f09-49f2-b6dc-da315c89237b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_for_edge_count_19818e22
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_for_edge_count_19818e22 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_drawable_simple_graph_has_edge_count_3n_minus_6_19818e22
      K hV hK hmax⟩