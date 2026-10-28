-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_ac816c5dcb924d25
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:53:52.380552+00:00
-- url     : https://prove2.me/submissions/9881825c-3442-433f-b9bf-03752e9076dd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨H.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
