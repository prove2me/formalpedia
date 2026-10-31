-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_c6dfb36f_1111_44f0_ab98_16407e8ce911_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:17:56.296818+00:00
-- url     : https://prove2.me/submissions/da845684-c290-4790-9e6a-b78c2e35e0f0

import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2 K hV hK hmax
