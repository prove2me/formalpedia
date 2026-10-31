-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:35:52.371243+00:00
-- url     : https://prove2.me/submissions/8602b748-5993-4359-9e07-5bf25d7875e1

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2 N hCard hN hMax
