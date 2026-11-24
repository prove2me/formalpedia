-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:21.649994+00:00
-- url     : https://prove2.me/submissions/e1e8d7cc-95b1-4036-a6be-f950097af38c

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
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ K' : SimpleGraph V,
      K'.Connected ∧
      HasPlanarDrawingOn K' ∧
      K.edgeSet.ncard <= K'.edgeSet.ncard := by
  obtain ⟨H0, hGH0, hH0, hle0, hMax0⟩ := WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc K hK
  have hC0 : H0.Connected := WilliamsonShmoys.maximal_planar_drawingOn_connected H0 hH0 hMax0 hCard
  exact ⟨H0, hC0, hH0, hle0⟩
