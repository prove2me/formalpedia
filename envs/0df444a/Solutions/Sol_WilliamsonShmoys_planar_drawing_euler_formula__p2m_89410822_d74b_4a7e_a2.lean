-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula__p2m_89410822_d74b_4a7e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:15.273841+00:00
-- url     : https://prove2.me/submissions/0370fcc8-c7c7-48fd-b68c-8ed4c7f8e467

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by
  classical
  letI : DecidableRel G.Adj := dG
  have hcard : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using
      hConn.card_vert_le_card_edgeSet_add_one
  refine ⟨G.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega