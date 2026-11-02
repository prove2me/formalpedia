-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_characteristic__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:42.222977+00:00
-- url     : https://prove2.me/submissions/4c523208-631e-4e80-b8a6-17cb1ca3a69e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 := by
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  have hle' : Fintype.card V ≤ K.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using hle
  refine ⟨K.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega