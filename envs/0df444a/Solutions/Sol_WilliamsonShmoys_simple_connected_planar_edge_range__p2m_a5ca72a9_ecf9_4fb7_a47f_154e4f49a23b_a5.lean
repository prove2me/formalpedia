-- Prove2me | solution 1 for WilliamsonShmoys.simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:14:05.187209+00:00
-- url     : https://prove2.me/submissions/eacccba6-e79a-41d8-8ea1-00634a6f87d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_connected_planar_edge_upper__p2m_7da2409a_cbf1_4fa5_b632_5ead272fc49b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V ∧
      Fintype.card V ≤ T.edgeSet.ncard + 1 := by
  constructor
  · exact WilliamsonShmoys.simple_connected_planar_edge_upper__p2m_7da2409a_cbf1_4fa5_b632_5ead272fc49b_a1
      T hdraw hconn hV
  · have hl : Nat.card V ≤ Nat.card T.edgeSet + 1 :=
      hconn.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card] using hl