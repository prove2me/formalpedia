-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:42.203404+00:00
-- url     : https://prove2.me/submissions/ca1b21fc-f75f-42e3-88ad-6c8d6165a42f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_one_step__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_one_step_extension__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧ M ≤ H := by
  exact WilliamsonShmoys.planar_connected_extension_of_one_step__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
    M hplanar
    (fun G hG u v huv =>
      WilliamsonShmoys.planar_drawing_one_step_extension__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
        G hG u v huv)