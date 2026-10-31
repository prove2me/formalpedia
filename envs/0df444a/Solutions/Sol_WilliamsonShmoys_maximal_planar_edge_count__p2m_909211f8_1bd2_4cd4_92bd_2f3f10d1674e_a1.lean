-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:07.255094+00:00
-- url     : https://prove2.me/submissions/75cafbeb-17b3-4e40-97aa-30da3cf61f01

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ W)
    (hV : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :
      W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
      W hW hV
  have hlower :
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
      W hW hmax hV
  omega
