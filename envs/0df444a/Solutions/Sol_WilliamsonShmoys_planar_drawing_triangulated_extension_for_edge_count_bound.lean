-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_extension_for_edge_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:34:12.721199+00:00
-- url     : https://prove2.me/submissions/083102de-58ec-423f-8c36-656b866e69e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_count_bound_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, M ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hML, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_bound_v2 M hM
  exact ⟨L, hML, hL,
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_count_bound_v2 L hL hCard hmax⟩