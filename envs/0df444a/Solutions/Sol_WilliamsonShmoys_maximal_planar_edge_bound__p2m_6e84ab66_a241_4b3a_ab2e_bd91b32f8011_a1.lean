-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:44:14.852752+00:00
-- url     : https://prove2.me/submissions/6cf7df31-c229-4c95-8c0b-51132a78f777

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (hplanar : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have hplanarBound :=
    WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_7ed45ce9_fab7_4799_9a3a_4afc5611b50c_a2
      H hplanar hcard
  have hNcard : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by omega
  have hFinsetBound :=
    WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
      H (inferInstance : DecidableRel H.Adj) hNcard
  omega