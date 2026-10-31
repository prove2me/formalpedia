-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:36:16.151985+00:00
-- url     : https://prove2.me/submissions/808c4c8d-a2c1-4a9a-a4f9-90fcddb5da16

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M :=
  WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1 G hG
