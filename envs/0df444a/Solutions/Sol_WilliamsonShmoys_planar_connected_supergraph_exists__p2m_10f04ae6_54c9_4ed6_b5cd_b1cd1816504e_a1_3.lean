-- Prove2me | solution 3 for WilliamsonShmoys.planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:34:52.949894+00:00
-- url     : https://prove2.me/submissions/d67a9acc-d6c8-4ede-86d2-c9175e6ae4e5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

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