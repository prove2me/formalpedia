-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:20:37.473289+00:00
-- url     : https://prove2.me/submissions/d0545eb7-20de-46e1-8a9b-796ac0790634

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1 H hH hcard hmax
