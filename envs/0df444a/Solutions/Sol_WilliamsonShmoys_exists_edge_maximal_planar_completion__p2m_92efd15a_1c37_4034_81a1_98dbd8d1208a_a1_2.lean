-- Prove2me | solution 2 for WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:52.982708+00:00
-- url     : https://prove2.me/submissions/c291a042-1ad4-43b5-8eaa-25157e400867

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.maximal_planar_supergraph N hN
