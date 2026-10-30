-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:27.529899+00:00
-- url     : https://prove2.me/submissions/623d3bc6-4641-438b-b673-b7fbee38a533
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ ¬ G ≤ H := by
  obtain ⟨u, v, G, hnotAdj, hHG, hGPlanar, hGAdj⟩ :=
    WilliamsonShmoys.planar_disconnected_has_bridge_extension__p2m_319c6fe2_72dc_4179_bbfd_8ad17647c43d_a1
      H hV hH hdisc
  refine ⟨G, hHG, hGPlanar, ?_⟩
  intro hGH
  exact hnotAdj (hGH hGAdj)