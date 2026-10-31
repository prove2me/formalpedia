-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:29:19.092046+00:00
-- url     : https://prove2.me/submissions/6da7d52b-2118-470c-9f0d-3b5ded5fb974

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_v2 Q hDraw hMax hCard
