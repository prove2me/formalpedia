-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:19:46.63229+00:00
-- url     : https://prove2.me/submissions/74c0a69d-a0c0-4051-9b6d-4313fb1152dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G <= H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) <=
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card) := by
  classical
  apply Finset.card_le_card
  exact SimpleGraph.edgeFinset_mono hGH