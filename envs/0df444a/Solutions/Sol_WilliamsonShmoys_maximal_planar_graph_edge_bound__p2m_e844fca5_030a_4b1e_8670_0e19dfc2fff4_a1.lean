-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_e844fca5_030a_4b1e_8670_0e19dfc2fff4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:26.260063+00:00
-- url     : https://prove2.me/submissions/d416fb62-d610-4dc1-bbdc-05a7398afcfa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := dK;
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  have hbound :=
    WilliamsonShmoys.planar_edgeSet_ncard_le_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
      K hn hK
  exact WilliamsonShmoys.edgeSet_ncard_le_to_edgeFinset_card_le__p2m_90141f6c_e00d_474f_bb06_5b30de1c5624_a1
    K dK hbound
