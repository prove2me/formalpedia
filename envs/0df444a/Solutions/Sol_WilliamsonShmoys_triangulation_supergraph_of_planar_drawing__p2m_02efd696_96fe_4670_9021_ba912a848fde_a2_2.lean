-- Prove2me | solution 2 for WilliamsonShmoys_triangulation_supergraph_of_planar_drawing__p2m_02efd696_96fe_4670_9021_ba912a848fde_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:06.59343+00:00
-- url     : https://prove2.me/submissions/6ec51dae-a086-4aef-a817-8f5086b43039

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
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨H0, hGH0, hH0, -, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc G hcard hdraw
  refine ⟨H0, hGH0, hH0, ?_⟩
  letI : DecidableRel H0.Adj := Classical.decRel H0.Adj
  show H0.edgeFinset.card + 6 = 3 * Fintype.card V
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
