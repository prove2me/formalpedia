-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:03.681796+00:00
-- url     : https://prove2.me/submissions/dec570d8-af44-417c-8c8f-688647ecee52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V),
      (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_d79776b6_af88_4e2b_abb0_db45e2831b04_a2
    K hK hconn hV