-- Prove2me | solution 1 for WilliamsonShmoys.planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:32:32.279998+00:00
-- url     : https://prove2.me/submissions/05db7056-d7c5-4f9b-bd0f-e7ea1d4865f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet →
        HasPlanarDrawingOn N → Set.Subset N.edgeSet M.edgeSet := by
  classical
  letI : Finite (SimpleGraph V) := inferInstance
  exact exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1
    (fun G H => Set.Subset G.edgeSet H.edgeSet)
    (by intro G; exact Set.Subset.rfl)
    (by intro G H K hGH hHK; exact Set.Subset.trans hGH hHK)
    HasPlanarDrawingOn L hL