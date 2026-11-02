-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:14.427754+00:00
-- url     : https://prove2.me/submissions/aaabee21-e581-4583-8bed-f8d80edf561c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     Exists fun f : Nat => Fintype.card V + f = N.edgeFinset.card + 2) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  change ∃ f : Nat, Fintype.card V + f = N.edgeFinset.card + 2
  have hle : Fintype.card V ≤ N.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨N.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega