-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:16:06.094965+00:00
-- url     : https://prove2.me/submissions/d08987b1-5684-4d0c-9073-8754643d220f

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_a4893b45
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_a4893b45 K hK hcard hmax
