-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_euler_face_count__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:34:15.043008+00:00
-- url     : https://prove2.me/submissions/3eeaa305-31dd-4486-a178-054465f92009

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
import Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, 0 < f ∧
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
      G hG hConn
  have hEdges : Fintype.card V ≤ G.edgeFinset.card + 1 :=
    WilliamsonShmoys.connected_card_le_edgeFinset_add_one__p2m_7f4c1ad2_4413_457d_ae8f_8936a6ba8a01_a3
      G hConn
  exact ⟨f, by omega, hEuler⟩