-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:52:42.360639+00:00
-- url     : https://prove2.me/submissions/19f2dacb-2bbc-4aa6-afef-1be702389f72

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_le_three_n_sub_six_from_planar_drawing
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    T.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  have h₁ := WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1 T T (le_refl T)
  have h₂ := WilliamsonShmoys.edge_count_le_three_n_sub_six_from_planar_drawing T hT hcard
  exact le_trans (Nat.add_le_add_right h₁ 6) h₂

