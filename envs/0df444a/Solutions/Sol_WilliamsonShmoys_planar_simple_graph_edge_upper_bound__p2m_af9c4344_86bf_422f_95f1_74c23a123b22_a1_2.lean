-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:09.636034+00:00
-- url     : https://prove2.me/submissions/175da048-560d-4d7c-b541-17e2aa3b07a1

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [DecidableRel L.Adj] (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) : L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc L hcard hL
  have e : L.edgeSet.ncard = L.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega
