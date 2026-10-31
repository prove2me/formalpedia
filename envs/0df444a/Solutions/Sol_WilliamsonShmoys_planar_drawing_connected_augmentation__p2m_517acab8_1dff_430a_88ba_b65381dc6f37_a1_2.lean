-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:38:28.572211+00:00
-- url     : https://prove2.me/submissions/a58b14b8-18dc-4c2f-bcee-05bafcadeddd

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_1794ae85

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, Z ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension_1794ae85 Z hZ hV
