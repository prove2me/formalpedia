-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:15:15.267018+00:00
-- url     : https://prove2.me/submissions/d10c1af3-e834-47f8-9a18-c2a23f898940

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2 G hG
