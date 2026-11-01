-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:42.797206+00:00
-- url     : https://prove2.me/submissions/65282272-1df4-47fa-ae06-092820706cfb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ faceCount : Nat,
      Fintype.card V + faceCount = K.edgeFinset.card + 2 := by
  classical
  have hedge : Fintype.card V ≤ K.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  exact ⟨K.edgeFinset.card + 2 - Fintype.card V, by omega⟩