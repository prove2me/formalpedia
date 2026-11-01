-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:16.299539+00:00
-- url     : https://prove2.me/submissions/6a27b56e-3d0b-4fa4-973d-70b7d6589093

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N = M := by
  exact WilliamsonShmoys.exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) L hL