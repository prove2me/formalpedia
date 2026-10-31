-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:48:21.593075+00:00
-- url     : https://prove2.me/submissions/7c96ecb1-4b5f-4462-a095-64979892ad9d

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_fixed_vertex_set

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet :=
  WilliamsonShmoys.exists_maximal_planar_extension_fixed_vertex_set N hN
