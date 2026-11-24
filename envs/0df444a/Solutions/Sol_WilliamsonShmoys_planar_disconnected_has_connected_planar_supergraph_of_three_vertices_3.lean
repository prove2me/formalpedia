-- Prove2me | solution 3 for WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph_of_three_vertices
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:48.975807+00:00
-- url     : https://prove2.me/submissions/bbf2a734-2b49-419b-b037-cbcf699741f8

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
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  refine ⟨H0, lt_of_le_of_ne hGH0 ?_, hC0, hH0⟩
  intro h
  apply hDisconnected
  rw [h]
  exact hC0
