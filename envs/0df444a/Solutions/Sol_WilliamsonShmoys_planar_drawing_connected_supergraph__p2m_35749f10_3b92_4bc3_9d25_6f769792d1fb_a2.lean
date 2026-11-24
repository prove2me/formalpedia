-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:20.055883+00:00
-- url     : https://prove2.me/submissions/08ccd18c-43d9-41ef-b90b-62cd134a38b7

import Mathlib
import Mathlib.Tactic
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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ H : SimpleGraph V, (∀ e, e ∈ M.edgeSet → e ∈ H.edgeSet) ∧ (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc M hMplanar
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  exact ⟨H0, fun e he => (SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0) he, fun u v => (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hC0.preconnected _ _), hH0⟩
