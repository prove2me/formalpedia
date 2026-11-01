-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:32.411491+00:00
-- url     : https://prove2.me/submissions/1f6a99f7-777f-464e-bdc9-4d8a9757575a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  exact WilliamsonShmoys.finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
    H HasPlanarDrawingOn hH
    (by
      intro G hG hDisconnected
      exact WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
        G hG hcard hDisconnected)
