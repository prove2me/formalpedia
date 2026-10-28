-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_euler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:38:46.371443+00:00
-- url     : https://prove2.me/submissions/0606f704-7e84-4ed5-807f-87b922868d9d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by 
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
