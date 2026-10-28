-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:32:27.143992+00:00
-- url     : https://prove2.me/submissions/5333bd80-a622-4fbb-903c-6f8153cad8ca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  have hcard : Fintype.card V ≤ K.edgeSet.ncard + 1 := by
    simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨K.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega