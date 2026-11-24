-- Prove2me | solution 2 for WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:05.819731+00:00
-- url     : https://prove2.me/submissions/3c83b50a-0b75-4049-b12f-7f0434763733

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
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  have h := WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc H hcard hdraw hmax
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  show H.edgeFinset.card + 6 = 3 * Fintype.card V
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
