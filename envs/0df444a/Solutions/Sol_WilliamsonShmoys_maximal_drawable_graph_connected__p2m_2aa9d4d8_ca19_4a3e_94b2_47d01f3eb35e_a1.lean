-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:45:19.866825+00:00
-- url     : https://prove2.me/submissions/b2d9fc2a-166c-44e7-986b-8ad966089fdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    L.Connected := by
  by_contra hNotConnected
  obtain ⟨M, hM, hLM, hStrict⟩ :=
    WilliamsonShmoys.disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
      L hL hCard hNotConnected
  exact hStrict (hMax M hM hLM)