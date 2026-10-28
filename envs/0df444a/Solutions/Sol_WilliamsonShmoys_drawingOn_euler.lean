-- Prove2me | solution 1 for WilliamsonShmoys.drawingOn_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:25:21.289095+00:00
-- url     : https://prove2.me/submissions/76177814-617a-4176-a8da-8746304685ff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  classical
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  have hedges : Fintype.card ↑G.edgeSet = G.edgeSet.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hle' : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa [hedges] using hle
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega