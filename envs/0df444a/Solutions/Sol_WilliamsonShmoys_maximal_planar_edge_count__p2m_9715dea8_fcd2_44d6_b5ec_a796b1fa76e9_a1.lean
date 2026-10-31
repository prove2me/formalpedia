-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:09.357997+00:00
-- url     : https://prove2.me/submissions/9925934f-39b7-41cf-a201-218ea3048cd9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hUpper :
      M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
      M hM hCard
  have hLower :
      3 * Fintype.card V ≤ M.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
      M hM hCard hMax
  omega