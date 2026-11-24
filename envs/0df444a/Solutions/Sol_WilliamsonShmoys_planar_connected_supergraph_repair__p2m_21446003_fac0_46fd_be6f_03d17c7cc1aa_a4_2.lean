-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:02.153871+00:00
-- url     : https://prove2.me/submissions/9c456f52-731e-4aad-94f4-61b81a808dae

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
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V,
      U.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc U hU
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  exact ⟨H0, hle0, fun u v => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected _ _), hH0⟩
