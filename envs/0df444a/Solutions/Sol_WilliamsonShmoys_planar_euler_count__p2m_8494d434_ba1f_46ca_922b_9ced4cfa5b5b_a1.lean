-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:57.458729+00:00
-- url     : https://prove2.me/submissions/2810140e-ddd4-4198-9059-94b071a6ea9d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hcard : Fintype.card V ≤ H.edgeSet.ncard + 1 := by
    simpa using hconnected.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega