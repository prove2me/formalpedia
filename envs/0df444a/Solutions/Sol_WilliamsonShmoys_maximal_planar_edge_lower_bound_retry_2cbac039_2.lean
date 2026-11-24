-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:56.493257+00:00
-- url     : https://prove2.me/submissions/a9a19710-7a89-4b0e-bb41-0fc5e8be68a0

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

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → M.edgeSet = L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  have hMax' : ∀ J : SimpleGraph _, L ≤ J → HasPlanarDrawingOn J → J ≤ L := by
    intro J hHJ hJ
    exact (SimpleGraph.edgeSet_inj.mp (hMax J hJ (SimpleGraph.edgeSet_subset_edgeSet.mpr hHJ))).le
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc L hCard hL hMax'
  omega
