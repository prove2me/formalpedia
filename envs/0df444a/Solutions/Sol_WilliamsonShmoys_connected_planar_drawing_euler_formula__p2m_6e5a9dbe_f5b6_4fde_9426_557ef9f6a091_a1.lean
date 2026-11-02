-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:40:31.890145+00:00
-- url     : https://prove2.me/submissions/ac81ec39-d4d8-4c6d-b226-55b6ce6f1083

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    Exists fun f : Nat => Fintype.card V + f = K.edgeFinset.card + 2 := by
  classical
  have hb := hconn.card_vert_le_card_edgeSet_add_one
  have hb' : Fintype.card V <= K.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using hb
  refine Exists.intro (K.edgeFinset.card + 1 - Fintype.card V + 1) ?_
  omega