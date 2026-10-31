-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:55.270969+00:00
-- url     : https://prove2.me/submissions/4c7e38f3-9c93-407d-9359-7b009e193f32

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
      L hL
  obtain hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
      M hM hCard hMax
  exact ⟨M, hLM, hM, hCount⟩