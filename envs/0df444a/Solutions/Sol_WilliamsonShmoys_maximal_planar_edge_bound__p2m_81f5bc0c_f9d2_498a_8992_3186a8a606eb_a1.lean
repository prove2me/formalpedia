-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:47.693577+00:00
-- url     : https://prove2.me/submissions/8d04ff04-2603-42e4-b1b1-ac218cb4e391

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9 N hN hCard hMax
