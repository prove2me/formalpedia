-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:38.154985+00:00
-- url     : https://prove2.me/submissions/ed303a0b-bc59-4df1-8109-dc4b09981895

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hcard : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    have h := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← H.edgeFinset_card] at h
    exact h
  refine ⟨H.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega