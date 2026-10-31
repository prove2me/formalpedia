-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:41.143821+00:00
-- url     : https://prove2.me/submissions/17b0b6e8-9e30-43f8-91a2-9741477198d6

import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q ≤ R →
        WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q :=
  WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1 P hP
