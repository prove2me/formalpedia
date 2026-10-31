-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:14.569041+00:00
-- url     : https://prove2.me/submissions/b89061df-bfce-4080-a445-6b2928af8a86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  rcases WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1 H hH with
    ⟨T, hHT, hT, hmax⟩
  exact ⟨T, hHT, hT,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1 T hV hT hmax⟩