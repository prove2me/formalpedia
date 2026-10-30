-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_dense_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:51:01.716058+00:00
-- url     : https://prove2.me/submissions/e7c0b53c-28f9-4f78-b516-630e8be65988

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_choose_maximal
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_has_dense_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_dense_supergraph_choose_maximal H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.planar_drawing_maximal_has_dense_edge_count K hV hK hmax⟩