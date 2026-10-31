-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:20.589775+00:00
-- url     : https://prove2.me/submissions/2920deac-117b-4803-b831-abf352ca3fa5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      (letI : DecidableRel L.Adj := dL
       H <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= H))
    (hcard : 3 <= Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hu :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
      H dH hH hcard
  have hl :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_760d336b_8795_40bc_8413_7180f98d62aa_a2
      H dH hH hconn hmax hcard
  omega