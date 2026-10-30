-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:02.020286+00:00
-- url     : https://prove2.me/submissions/29e786f2-71ce-4a7b-8783-86547a70e069
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2 N hN hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2 N hN hCard hMax
  omega