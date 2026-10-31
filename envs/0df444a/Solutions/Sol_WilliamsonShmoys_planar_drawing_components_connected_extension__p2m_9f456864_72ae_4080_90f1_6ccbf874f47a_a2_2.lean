-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:39:17.908136+00:00
-- url     : https://prove2.me/submissions/9853438b-8676-43ef-9591-ea3a472cf07d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_1794ae85

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension_1794ae85 L hL hCard
