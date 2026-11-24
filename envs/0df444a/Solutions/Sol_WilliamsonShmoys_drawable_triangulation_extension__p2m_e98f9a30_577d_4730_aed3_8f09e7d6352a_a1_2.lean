-- Prove2me | solution 2 for WilliamsonShmoys.drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:28.275924+00:00
-- url     : https://prove2.me/submissions/c966ae80-e4b4-4815-8e21-1b0ebd48e9d3

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
      3 * (Fintype.card V - 2) ≤ H.edgeSet.ncard := by
  obtain ⟨H0, hGH0, hH0, hle, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc K hV hK
  exact ⟨H0, hGH0, hH0, by omega⟩
