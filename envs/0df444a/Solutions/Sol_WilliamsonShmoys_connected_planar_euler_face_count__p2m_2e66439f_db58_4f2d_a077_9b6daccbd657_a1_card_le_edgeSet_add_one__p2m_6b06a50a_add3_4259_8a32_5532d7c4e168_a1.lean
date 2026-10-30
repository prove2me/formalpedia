-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:39.58718+00:00
-- url     : https://prove2.me/submissions/6bea9d47-4348-451e-ad53-ed8cfe071fb8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hConnected : G.Connected) : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  classical
  have h := hConnected.card_vert_le_card_edgeSet_add_one
  simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using h