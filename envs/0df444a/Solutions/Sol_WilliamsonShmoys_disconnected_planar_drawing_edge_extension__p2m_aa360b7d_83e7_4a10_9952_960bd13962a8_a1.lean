-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:33.60281+00:00
-- url     : https://prove2.me/submissions/33a07a7f-1b01-4bc5-a9f6-fe60a75d06bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
import Theorems.Thm_WilliamsonShmoys_planar_join_unreachable_components__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) (hDisc : ¬ L.Connected) :
    ∃ N : SimpleGraph V,
      L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ ¬ N ≤ L := by
  obtain ⟨u, v, huv, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
      L hV hDisc
  obtain ⟨N, hLN, hN, _hEdge, hStrict⟩ :=
    WilliamsonShmoys.planar_join_unreachable_components__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
      L hL u v huv hUnreachable
  exact ⟨N, hLN, hN, hStrict⟩