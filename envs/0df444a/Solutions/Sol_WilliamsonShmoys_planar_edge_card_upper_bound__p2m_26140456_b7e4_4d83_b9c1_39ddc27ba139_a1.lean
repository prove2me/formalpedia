-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:04.569803+00:00
-- url     : https://prove2.me/submissions/9f9f57e8-2f3d-407a-ba97-fa48f4311006

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, htri⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1
      G hG hcard
  letI : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨hsub, hcardH⟩ := htri
  have hle := Finset.card_le_card hsub
  rw [hcardH] at hle
  exact hle