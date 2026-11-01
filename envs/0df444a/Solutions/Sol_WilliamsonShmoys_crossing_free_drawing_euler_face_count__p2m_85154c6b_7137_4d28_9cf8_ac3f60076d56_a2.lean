-- Prove2me | solution 1 for WilliamsonShmoys.crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:04.971504+00:00
-- url     : https://prove2.me/submissions/5d58e8c2-7b93-453c-b1c2-9c01ee9cb8f5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    exists f : Nat, H.edgeSet.ncard + 2 = Fintype.card V + f := by
  have hbound : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
    simpa using hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ H.edgeSet.ncard + 2 := by omega
  obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨f, hf⟩