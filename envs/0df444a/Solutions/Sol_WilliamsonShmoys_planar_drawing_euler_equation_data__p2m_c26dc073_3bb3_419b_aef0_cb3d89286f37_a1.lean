-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:07.522252+00:00
-- url     : https://prove2.me/submissions/66c54528-3f79-4b27-bda6-d3e4352570a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : Nat,
       Fintype.card V + f = H.edgeFinset.card + 2) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hle := WilliamsonShmoys.connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3 H hconn
  refine ⟨H.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega