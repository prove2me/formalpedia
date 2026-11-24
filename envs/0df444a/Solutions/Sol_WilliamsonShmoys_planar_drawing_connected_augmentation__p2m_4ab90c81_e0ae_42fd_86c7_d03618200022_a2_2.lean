-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:07.335489+00:00
-- url     : https://prove2.me/submissions/6be365de-cc87-4c06-98fa-a4b782c79790

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
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V), ∃ (dM : DecidableRel M.Adj),
      (letI : DecidableRel M.Adj := dM
       HasPlanarDrawingOn M ∧
       N.edgeFinset.card ≤ M.edgeFinset.card ∧
       M.Connected) := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc N hN
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hcard
  refine ⟨H0, Classical.decRel _, hH0, ?_, hC0⟩
  simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at *
  exact hle0
