-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:12.762746+00:00
-- url     : https://prove2.me/submissions/2a2dfe51-7979-4fbb-a631-3baf87908e23

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
    K.edgeSet.ncard ≤ 3 * (Fintype.card V - 2) := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc K hV hK
  omega
