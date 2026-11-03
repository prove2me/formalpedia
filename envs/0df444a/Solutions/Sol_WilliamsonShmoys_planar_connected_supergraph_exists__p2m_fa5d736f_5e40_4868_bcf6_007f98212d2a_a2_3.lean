-- Prove2me | solution 3 for WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:24:38.610871+00:00
-- url     : https://prove2.me/submissions/73a2a23d-e276-4960-872b-860e3fa614af

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1 H hH hcard