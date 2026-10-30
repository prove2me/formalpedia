-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:03.35244+00:00
-- url     : https://prove2.me/submissions/93555aee-1382-4e34-b013-69825c082dee

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hConnected : G.Connected) :
    Exists fun f : Nat => Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hcard : Fintype.card V <= G.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1 G hConnected
  refine Exists.intro ((G.edgeSet.ncard + 2) - Fintype.card V) ?_
  omega