-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:59.394439+00:00
-- url     : https://prove2.me/submissions/b1c1f632-bec5-4b7f-81e0-62805046d7fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact WilliamsonShmoys.planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
    G hG hV
    (fun K _ hK hDisconnected =>
      WilliamsonShmoys.planar_drawing_disconnected_edge_extension__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
        K hK hV hDisconnected)