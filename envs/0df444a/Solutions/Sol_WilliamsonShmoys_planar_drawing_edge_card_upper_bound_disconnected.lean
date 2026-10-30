-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_card_upper_bound_disconnected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:34:54.363498+00:00
-- url     : https://prove2.me/submissions/7fb3efda-816d-43b0-a685-a79a414ccaa5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_connected__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ S.Connected) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hTConnected, hTPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
      S hS hCard hNotConnected
  exact (WilliamsonShmoys.planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
      S T hST).trans
    (WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
      T hTPlanar hCard hTConnected)
