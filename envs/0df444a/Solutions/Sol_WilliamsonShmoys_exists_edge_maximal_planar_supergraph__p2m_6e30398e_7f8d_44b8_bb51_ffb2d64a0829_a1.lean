-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:26:43.196053+00:00
-- url     : https://prove2.me/submissions/c9c24b41-f2cc-48b7-a6c2-f7846701ea74

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = M.edgeSet :=
  WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b N hN
