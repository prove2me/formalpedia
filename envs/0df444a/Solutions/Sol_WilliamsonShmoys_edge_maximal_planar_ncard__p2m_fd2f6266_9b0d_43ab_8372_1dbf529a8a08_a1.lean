-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:12:37.181859+00:00
-- url     : https://prove2.me/submissions/43305de5-5623-40d2-a152-24388da48f16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1 N hCard hN
  have hLower := WilliamsonShmoys.maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1 N hCard hN hMax
  omega