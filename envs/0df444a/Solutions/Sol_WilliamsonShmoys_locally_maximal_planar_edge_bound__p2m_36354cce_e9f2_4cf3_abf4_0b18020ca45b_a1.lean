-- Prove2me | solution 1 for WilliamsonShmoys.locally_maximal_planar_edge_bound__p2m_36354cce_e9f2_4cf3_abf4_0b18020ca45b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:49.343183+00:00
-- url     : https://prove2.me/submissions/a3426d25-7d40-467a-9b03-b2fd5a078a08

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hNoOneEdgeExtension : ∀ L : SimpleGraph V, K ≤ L →
      L.edgeSet.ncard = K.edgeSet.ncard + 1 →
      WilliamsonShmoys.HasPlanarDrawingOn L → False) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hMax := WilliamsonShmoys.local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
    K hDraw hNoOneEdgeExtension
  have hCount := WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
    K hDraw hMax hCard
  omega