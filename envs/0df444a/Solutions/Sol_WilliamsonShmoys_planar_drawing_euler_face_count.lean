-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:49:01.304251+00:00
-- url     : https://prove2.me/submissions/4ec04d3a-5a19-4b42-87c7-2fd12c320df2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      (Fintype.card V : Int) - (H.edgeSet.ncard : Int) + (f : Int) = 2 := by 
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  push_cast [show Fintype.card V ≤ H.edgeSet.ncard + 2 by omega]
  ring
