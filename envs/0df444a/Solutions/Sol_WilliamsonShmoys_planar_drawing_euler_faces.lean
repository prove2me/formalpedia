-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_faces
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:40:47.322105+00:00
-- url     : https://prove2.me/submissions/9b8daec9-5f11-448a-8222-fe3879434d58

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun f : Nat => K.edgeSet.ncard + 2 = Fintype.card V + f := by
  have hcard : Fintype.card V ≤ K.edgeSet.ncard + 2 := by
    have h := hconn.card_vert_le_card_edgeSet_add_one
    have h' : Fintype.card V ≤ Nat.card K.edgeSet + 1 := by
      simpa [Nat.card_eq_fintype_card] using h
    have h'' : Nat.card K.edgeSet ≤ K.edgeSet.ncard := by
      simp
    omega
  refine ⟨K.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega