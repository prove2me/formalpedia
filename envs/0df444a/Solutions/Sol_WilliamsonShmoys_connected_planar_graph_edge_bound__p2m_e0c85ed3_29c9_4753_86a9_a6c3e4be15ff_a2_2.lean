-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:12.02085+00:00
-- url     : https://prove2.me/submissions/f714a5eb-1880-49c6-b3d9-ea3a4bb7dff6

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
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  show G.edgeFinset.card + 6 ≤ 3 * Fintype.card V
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hcard hdraw
  have e : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
