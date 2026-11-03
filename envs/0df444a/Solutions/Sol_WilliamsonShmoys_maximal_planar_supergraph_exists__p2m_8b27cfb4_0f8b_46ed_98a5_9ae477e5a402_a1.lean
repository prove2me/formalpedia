-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:09:56.693192+00:00
-- url     : https://prove2.me/submissions/82649c82-87d2-4058-812f-6e50b13a3fba

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K <= L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K :=
  WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1 G hG