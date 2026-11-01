-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:36.154312+00:00
-- url     : https://prove2.me/submissions/676d4c73-5f58-43ee-b997-5f22cb87cfe7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1 H hH hcard
