-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:12.474389+00:00
-- url     : https://prove2.me/submissions/c70a5e55-1c22-4a9d-b547-3161a5d53ed6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hcard :=
    WilliamsonShmoys.connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1 G hconn
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega