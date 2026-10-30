-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:49.000077+00:00
-- url     : https://prove2.me/submissions/d36648cd-0f4f-4d82-b0ce-1b22cfaf8d35

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected) (hDraw : HasPlanarDrawingOn H) :
    ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by
  have hle : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
    simpa using hConn.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega