-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:10:35.165057+00:00
-- url     : https://prove2.me/submissions/0cc7db00-66a9-413f-ace9-a68ac80e7962

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = P.edgeSet.ncard + 2 := by
  classical
  have h := hPconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  have h2 : (P.edgeSet).ncard = Nat.card P.edgeSet := (Nat.card_coe_set_eq _).symm
  exact ⟨P.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
