-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:51.675276+00:00
-- url     : https://prove2.me/submissions/e362bc4a-6a36-4f70-899a-cc382e1302c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_join_unreachable_vertices__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K' ≠ K := by
  obtain ⟨u, v, huv, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2
      K hV hDisconnected
  obtain ⟨K', hSub, hDrawing, hDifferent, hEdge⟩ :=
    WilliamsonShmoys.planar_drawing_join_unreachable_vertices__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
      K hK huv hUnreachable
  exact ⟨K', hSub, hDrawing, hDifferent⟩