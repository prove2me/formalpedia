-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_euler_face_count__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:04.444244+00:00
-- url     : https://prove2.me/submissions/8a8b3a12-1c83-4245-a058-87657e241d95

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hbound : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
    simpa [Nat.card_eq_fintype_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega