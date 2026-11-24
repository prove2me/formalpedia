-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:03:27.705041+00:00
-- url     : https://prove2.me/submissions/ecf8597f-3441-4712-b867-1def08fd5e37

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
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    exact SimpleGraph.edgeSet_subset_edgeSet.mp (hMax J (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) hJ)
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hCard hH hMax'
  omega
