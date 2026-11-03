-- Prove2me | solution 1 for WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:38:46.827877+00:00
-- url     : https://prove2.me/submissions/e2b3686b-5a17-4a66-b629-478d9a6c4922

import Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K :=
  WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2 H hH