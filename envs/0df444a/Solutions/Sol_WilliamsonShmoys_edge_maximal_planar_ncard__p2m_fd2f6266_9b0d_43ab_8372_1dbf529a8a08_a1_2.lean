-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_ncard__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:37.815719+00:00
-- url     : https://prove2.me/submissions/269f8c7b-98d9-4ea1-aac1-b433f05628ad

import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1 N hCard hN hMax
