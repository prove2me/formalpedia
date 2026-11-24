-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connect_components
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:22.755933+00:00
-- url     : https://prove2.me/submissions/5f652172-0ec5-4f27-a4fd-abc52861bd0f

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
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc H hH
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hV
  exact ⟨H0, hle0, hH0, hC0⟩
