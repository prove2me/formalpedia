-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:25.312207+00:00
-- url     : https://prove2.me/submissions/a0fc257b-5f98-4f5a-8ceb-f816e0b94990

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M = L := by
  exact WilliamsonShmoys.maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1
    WilliamsonShmoys.HasPlanarDrawingOn K hplanar