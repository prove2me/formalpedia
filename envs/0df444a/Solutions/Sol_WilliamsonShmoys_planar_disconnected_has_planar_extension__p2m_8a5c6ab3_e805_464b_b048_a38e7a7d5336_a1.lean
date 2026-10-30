-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:28.236862+00:00
-- url     : https://prove2.me/submissions/9f411cb8-cb1b-4904-9b4a-5fd118b243fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hdisc : ¬ H.Connected) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ ¬ G ≤ H := by
  obtain ⟨G, u, v, huv, hnot, hHG, hGp, hGuv, _hchar⟩ :=
    WilliamsonShmoys.planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1
      H hH hdisc
  refine ⟨G, hHG, hGp, ?_⟩
  intro hGH
  exact hnot (hGH hGuv)