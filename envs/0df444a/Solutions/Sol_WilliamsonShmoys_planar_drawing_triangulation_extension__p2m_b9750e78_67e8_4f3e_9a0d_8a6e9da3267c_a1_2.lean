-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:31.384418+00:00
-- url     : https://prove2.me/submissions/bcb2b34f-f6c4-4acd-a212-4fce17ad2163

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
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * (Fintype.card V - 2) := by
  obtain ⟨H0, hGH0, hH0, hle, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc K hV hK
  exact ⟨H0, hGH0, hH0, hle, by omega⟩
