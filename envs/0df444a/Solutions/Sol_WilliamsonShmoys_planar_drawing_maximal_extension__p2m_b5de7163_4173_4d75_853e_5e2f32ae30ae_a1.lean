-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:57.536758+00:00
-- url     : https://prove2.me/submissions/2e20df30-84d2-4762-8231-d3e42b4e33ca

import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet :=
  WilliamsonShmoys.planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde K hplanar
