-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:42.171986+00:00
-- url     : https://prove2.me/submissions/07a0bdc8-91a2-4654-8532-1b885a928c67

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hsmall : Fintype.card V < 3) :
    L.edgeFinset.card ≤ (Fintype.card V).choose 2 := by
  letI : DecidableRel L.Adj := dL
  exact SimpleGraph.card_edgeFinset_le_card_choose_two (G := L)