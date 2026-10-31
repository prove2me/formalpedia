-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:05.404657+00:00
-- url     : https://prove2.me/submissions/24333d6e-7261-499c-988d-fc92ec96e697

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1 K hK hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1 K hK hCard hMax
  omega