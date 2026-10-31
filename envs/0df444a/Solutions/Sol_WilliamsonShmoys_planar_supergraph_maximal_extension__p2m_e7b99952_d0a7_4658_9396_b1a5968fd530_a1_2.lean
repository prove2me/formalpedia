-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_e7b99952_d0a7_4658_9396_b1a5968fd530_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:26:40.807704+00:00
-- url     : https://prove2.me/submissions/2c97640f-bd03-48e7-a52d-a8fa14e215c6

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ M : SimpleGraph V,
        N.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = N.edgeSet :=
  WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b K hK
