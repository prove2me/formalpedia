-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:50.793042+00:00
-- url     : https://prove2.me/submissions/946c2f7f-8429-4cf0-b31b-3cbd62deea26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_iterate_bridges__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  apply WilliamsonShmoys.planar_drawing_iterate_bridges__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1 H hH
  intro K hHK hK hKnot
  exact WilliamsonShmoys.planar_drawing_bridge_step__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1 K hK hKnot