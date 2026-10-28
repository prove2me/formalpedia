-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_dense_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:53:42.513111+00:00
-- url     : https://prove2.me/submissions/f56b5eaf-e0fa-4c76-9ec3-1de73f650535
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_finite_choice
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound_via_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_finite_choice H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_drawable_edge_lower_bound_via_euler K hK hCard hMax⟩