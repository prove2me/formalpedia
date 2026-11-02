-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_faces__p2m_6360b5b8_545a_4187_945d_5d0aa3896a85_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T21:17:50.35548+00:00
-- url     : https://prove2.me/submissions/cfd848c0-694c-4d1e-98b8-21131a626188

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun f : Nat => Fintype.card V + f = K.edgeFinset.card + 2 := by
  letI := dK
  have hconnCard : Nat.card V ≤ Nat.card K.edgeSet + 1 :=
    hconn.card_vert_le_card_edgeSet_add_one
  have hcard : Fintype.card V ≤ K.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← K.edgeFinset_card] using hconnCard
  have hcard' : Fintype.card V ≤ K.edgeFinset.card + 2 := by omega
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega
