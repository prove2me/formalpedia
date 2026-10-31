-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:30.611462+00:00
-- url     : https://prove2.me/submissions/1bbd8e66-4b42-489c-81c1-2037f31d1b12

import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_2d69255633d74159

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ M.edgeSet :=
  WilliamsonShmoys.planar_completion_maximal_2d69255633d74159 N hN
