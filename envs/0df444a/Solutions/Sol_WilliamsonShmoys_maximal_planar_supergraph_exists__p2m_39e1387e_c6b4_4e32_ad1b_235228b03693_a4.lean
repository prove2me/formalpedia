-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:31.637918+00:00
-- url     : https://prove2.me/submissions/e83cf583-f528-4587-805c-6351cb0c0007

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  exact WilliamsonShmoys.exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1
    H HasPlanarDrawingOn hH