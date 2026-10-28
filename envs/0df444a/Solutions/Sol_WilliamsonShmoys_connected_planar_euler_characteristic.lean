-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:15:39.277188+00:00
-- url     : https://prove2.me/submissions/aed59bc0-6584-4b83-9d33-f19e3993ded5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 := by
  classical
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (K.edgeSet).ncard = Nat.card K.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨K.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
end WilliamsonShmoys

