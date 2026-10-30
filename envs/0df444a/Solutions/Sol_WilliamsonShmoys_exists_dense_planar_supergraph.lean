-- Prove2me | solution 1 for WilliamsonShmoys.exists_dense_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:09:53.716639+00:00
-- url     : https://prove2.me/submissions/256abedc-5f00-4dc3-90b7-e8a926d6fd02

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_f274a542
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_f274a542

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_f274a542 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_f274a542 L hV hL hmax⟩