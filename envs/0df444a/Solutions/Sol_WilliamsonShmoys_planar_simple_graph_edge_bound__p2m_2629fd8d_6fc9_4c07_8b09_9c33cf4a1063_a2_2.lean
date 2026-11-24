-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:09.116702+00:00
-- url     : https://prove2.me/submissions/5851c3e8-3eb2-4a0e-9c68-83eb225dacc4

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hcard hG
  have e : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
