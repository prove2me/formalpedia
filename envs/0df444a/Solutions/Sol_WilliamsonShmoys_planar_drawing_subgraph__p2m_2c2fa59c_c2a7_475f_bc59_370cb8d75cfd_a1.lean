-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:15:30.445992+00:00
-- url     : https://prove2.me/submissions/f6514bfc-15cb-4ef9-b9f4-88db99aa58cc

import Theorems.Thm_WilliamsonShmoys_planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G :=
  WilliamsonShmoys.planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761 hGH hH
