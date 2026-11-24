-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_b74a49f4
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:50.811622+00:00
-- url     : https://prove2.me/submissions/d0eb25c9-f692-4390-bfcd-163c72646928

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc K hK
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hCard
  exact ⟨H0, hGH0, hle0, hC0, hH0⟩
