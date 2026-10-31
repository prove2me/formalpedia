-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:16.517514+00:00
-- url     : https://prove2.me/submissions/d3b12d95-b5ec-40fc-b5a3-23566e614dbe

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hGJ, hDrawJ, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
      G hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
      J hDrawJ hMax hCard
  exact ⟨J, hGJ, hDrawJ, hCount⟩