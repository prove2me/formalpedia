-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:40.082961+00:00
-- url     : https://prove2.me/submissions/92562cdc-f166-4c60-a03e-e52fa8e57be1

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
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ (H : SimpleGraph V), ∃ (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        (letI : DecidableRel H.Adj := dH
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨H0, hGH0, hH0, -, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc G hcard hG
  refine ⟨H0, Classical.decRel _, hH0, hGH0, ?_⟩
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  omega
