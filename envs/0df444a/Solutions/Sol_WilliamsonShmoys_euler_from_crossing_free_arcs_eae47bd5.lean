-- Prove2me | solution 1 for WilliamsonShmoys.euler_from_crossing_free_arcs_eae47bd5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:39:39.8062+00:00
-- url     : https://prove2.me/submissions/f85a3854-f777-497c-87da-880282c27d8d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false


open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
