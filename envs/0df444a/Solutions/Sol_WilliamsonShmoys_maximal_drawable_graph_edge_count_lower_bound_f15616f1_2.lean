-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_f15616f1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:59.224654+00:00
-- url     : https://prove2.me/submissions/a4a2dc6c-9ae5-4b2a-95c1-1c8dd1ddb38a

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
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
      H ≤ J → H = J) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  have hMax' : ∀ J : SimpleGraph _, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
    intro J hHJ hJ
    exact (hmax J hJ hHJ).ge
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hCard hH hMax'
  omega
