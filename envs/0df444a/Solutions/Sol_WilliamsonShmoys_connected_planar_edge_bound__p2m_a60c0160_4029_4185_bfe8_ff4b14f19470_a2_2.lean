-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:11.325785+00:00
-- url     : https://prove2.me/submissions/69926e01-3dca-420b-9868-c24b5f8f75ca

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
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc H hn hdraw
  have e : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
