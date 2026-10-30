-- Prove2me | solution 1 for WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:42:50.285973+00:00
-- url     : https://prove2.me/submissions/963ffdc1-db70-4ff9-9603-62564bf36641
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 ∧
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  constructor
  · have h := hconn.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card] using h
  · exact WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1
      G hG hV hconn