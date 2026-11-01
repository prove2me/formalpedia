-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:28.96914+00:00
-- url     : https://prove2.me/submissions/f7b72501-9233-4fb6-8504-825b340df247

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     ∃ f : ℕ, Fintype.card V + f = G.edgeFinset.card + 2) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hle : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨G.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega