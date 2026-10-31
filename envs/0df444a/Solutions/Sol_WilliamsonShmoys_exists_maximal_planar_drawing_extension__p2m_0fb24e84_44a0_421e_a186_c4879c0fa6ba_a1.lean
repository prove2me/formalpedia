-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:44:06.982981+00:00
-- url     : https://prove2.me/submissions/a9f466e9-e0c2-4f47-a38c-660fa69ec1c8

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet :=
  WilliamsonShmoys.exists_maximal_planar_drawing_extension_00187ed1_118c_4569_ae21_cc59aa929691 K hDraw
