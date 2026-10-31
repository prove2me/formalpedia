-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:48:04.386994+00:00
-- url     : https://prove2.me/submissions/b10a780e-42bc-4c4d-8fc9-4b1c25da4432

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H :=
  WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1 G hG
