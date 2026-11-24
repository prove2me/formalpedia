-- Prove2me | solution 3 for WilliamsonShmoys.planar_simple_graph_disconnected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:08.50465+00:00
-- url     : https://prove2.me/submissions/d9381e45-e40b-48aa-8ebe-5fd009489f6c

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : ¬ G.Connected) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hcard hG
  have e : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
