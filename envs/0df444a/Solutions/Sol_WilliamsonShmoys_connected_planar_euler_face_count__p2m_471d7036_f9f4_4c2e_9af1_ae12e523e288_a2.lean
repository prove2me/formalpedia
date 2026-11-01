-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:01:00.609116+00:00
-- url     : https://prove2.me/submissions/c4eb9a53-3e85-4d7b-85f4-fe0580ef3200

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hle : Fintype.card V ≤ K.edgeFinset.card + 2 := by
    have h := hconn.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      (Nat.le_succ_of_le h)
  exact ⟨K.edgeFinset.card + 2 - Fintype.card V, Nat.add_sub_of_le hle⟩