-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:49.173055+00:00
-- url     : https://prove2.me/submissions/ef3dc725-005c-4484-9579-665dff0e3e90

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hle : Fintype.card V ≤ K.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega