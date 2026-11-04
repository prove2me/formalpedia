-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:51:19.805429+00:00
-- url     : https://prove2.me/submissions/896eaf95-a923-4a4e-9b48-5e81843c3c2c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_edge_upper_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1 H hV hH
  have hl := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1 H hV hH hmax
  exact Nat.le_antisymm hu hl