-- Prove2me | solution 2 for WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:45.960803+00:00
-- url     : https://prove2.me/submissions/4ec57d63-5242-4006-8337-926ca78a5813

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeFinset.card + 6 := by
  obtain ⟨K, hHK, hK, -, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc H hcard hH
  refine ⟨K, Classical.decRel _, hHK, hK, ?_⟩
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
