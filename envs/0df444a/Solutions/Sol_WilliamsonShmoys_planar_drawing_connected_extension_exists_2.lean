-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:29:19.521093+00:00
-- url     : https://prove2.me/submissions/5f0da3f6-384e-45e7-8479-a3514e0af3cf

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧ Z.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Z :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 Y hV hY
