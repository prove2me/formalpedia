-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:52.906005+00:00
-- url     : https://prove2.me/submissions/c604cff8-2500-4508-82f0-36c3c4d49a42

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
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hMax' : ∀ J : SimpleGraph _, M ≤ J → HasPlanarDrawingOn J → J ≤ M := by
    intro J hHJ hJ
    exact SimpleGraph.edgeSet_subset_edgeSet.mp (hMax J (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ) hJ)
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc M hV hM hMax'
  omega
