-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:37:45.922996+00:00
-- url     : https://prove2.me/submissions/8de7e083-db45-4cfd-af86-c27cdf65a433

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa [Set.ncard] using hcard
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega