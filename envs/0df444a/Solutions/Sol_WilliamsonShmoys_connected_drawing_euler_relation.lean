-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_relation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:03:52.989185+00:00
-- url     : https://prove2.me/submissions/7de3857e-c802-4b86-af77-87561aed72ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hle : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega