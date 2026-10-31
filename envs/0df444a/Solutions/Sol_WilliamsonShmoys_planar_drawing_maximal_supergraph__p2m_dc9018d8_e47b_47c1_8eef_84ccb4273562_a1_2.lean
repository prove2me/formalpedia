-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:16:17.648235+00:00
-- url     : https://prove2.me/submissions/12531141-45cc-45bc-b9b9-bbe6e054123c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ T : SimpleGraph V, G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T :=
  WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws G hG
