-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_maximal_extension__p2m_8348399b_8cb6_45dd_ab73_26e7cc43a44d_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:30.733312+00:00
-- url     : https://prove2.me/submissions/5d4116f2-14f6-48fb-bdbb-68d52c8d770e

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
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H0, hGH0, hH0, hle, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc M hCard hM
  exact ⟨H0, SimpleGraph.edgeSet_subset_edgeSet.mpr hGH0, by omega⟩
