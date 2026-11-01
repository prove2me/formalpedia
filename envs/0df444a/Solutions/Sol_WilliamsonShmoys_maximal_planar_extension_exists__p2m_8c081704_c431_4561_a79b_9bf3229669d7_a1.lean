-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:47.094745+00:00
-- url     : https://prove2.me/submissions/855fa40f-34f7-4cc3-ab06-8da43deb4cbe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊆ P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        P.edgeSet = N.edgeSet := by
  refine WilliamsonShmoys.finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
    (Q := WilliamsonShmoys.HasPlanarDrawingOn) ?_ M hM
  intro G H hHG hG
  exact WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1 hHG hG