-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:15:24.373327+00:00
-- url     : https://prove2.me/submissions/a2e7f7a8-c6bc-43d1-8e34-6c237a9e31db

import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G :=
  WilliamsonShmoys.planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1 hGH hH
