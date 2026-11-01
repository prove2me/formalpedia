-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_64019286_52a7_4945_b306_7d1954508408_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:15:32.308524+00:00
-- url     : https://prove2.me/submissions/cbb7e6d0-788e-4ebf-b8c7-f399258b2656

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_b74a49f4
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_card_b74a49f4 K hK hV hmax
