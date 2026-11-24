-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_has_triangulated_extension__p2m_055aa8e4_db8a_47ed_b733_513d02bcef62_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:29.476807+00:00
-- url     : https://prove2.me/submissions/172753f8-72b5-4461-bba3-0abd495bdb58

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
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H0, hGH0, hH0, hle, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc H hCard hH
  exact ⟨H0, SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0, hH0, by omega⟩
