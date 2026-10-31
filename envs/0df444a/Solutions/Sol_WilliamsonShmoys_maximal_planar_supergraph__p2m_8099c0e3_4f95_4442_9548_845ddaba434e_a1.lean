-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:50:12.8643+00:00
-- url     : https://prove2.me/submissions/f750518c-0b7f-494f-bae7-5c6550695bb1

import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :=
  WilliamsonShmoys.edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2 K hDraw
