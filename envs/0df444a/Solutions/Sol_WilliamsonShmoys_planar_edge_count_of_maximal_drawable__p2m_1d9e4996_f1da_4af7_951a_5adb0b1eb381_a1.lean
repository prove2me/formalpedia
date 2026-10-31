-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:31.985054+00:00
-- url     : https://prove2.me/submissions/b371e1bc-daa2-4320-9b89-0b84c98da37d

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → HasPlanarDrawingOn Q → Set.Subset Q.edgeSet P.edgeSet) : P.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2 P hP hCard hmax
