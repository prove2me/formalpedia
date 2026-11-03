-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_64019286_52a7_4945_b306_7d1954508408_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:58:31.424402+00:00
-- url     : https://prove2.me/submissions/a7b73f00-e36e-4f28-b6a6-af9c2af29318

import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_for_f2fc27dd
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_for_f2fc27dd H hH