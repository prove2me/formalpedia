-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:54.557801+00:00
-- url     : https://prove2.me/submissions/fe1b3f6b-99dc-4475-9df7-d35e7b8dd785

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
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  have hMax' : ∀ J : SimpleGraph _, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hHJ hJ
    exact (SimpleGraph.edgeSet_inj.mp (hMax J (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) hJ)).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc M hV hM hMax'
  omega
