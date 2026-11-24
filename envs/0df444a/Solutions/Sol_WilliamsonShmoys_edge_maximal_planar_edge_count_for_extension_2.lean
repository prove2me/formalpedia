-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_edge_count_for_extension
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:50:54.287795+00:00
-- url     : https://prove2.me/submissions/749710c8-e9e4-493a-98b5-c8b9c51237ac

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → J.edgeSet ⊆ K.edgeSet → K.edgeSet = J.edgeSet) : J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hMax' : ∀ J0 : SimpleGraph V, J ≤ J0 → HasPlanarDrawingOn J0 → J0 ≤ J := by
    intro J0 hJJ0 hJ0
    exact (SimpleGraph.edgeSet_inj.mp (hmax J0 hJ0 (SimpleGraph.edgeSet_subset_edgeSet.mpr hJJ0))).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc J hV hJ hMax'
  omega
