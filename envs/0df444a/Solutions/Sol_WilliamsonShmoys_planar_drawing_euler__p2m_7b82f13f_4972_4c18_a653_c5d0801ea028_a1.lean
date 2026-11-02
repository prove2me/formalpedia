-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:37.290707+00:00
-- url     : https://prove2.me/submissions/5b058f83-8f5b-4fa4-a17d-88762de36c27

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun f : Nat => H.edgeFinset.card + 2 = Fintype.card V + f := by
  classical
  letI : DecidableRel H.Adj := dH
  have hle : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega