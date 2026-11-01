-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:13.754435+00:00
-- url     : https://prove2.me/submissions/73e96a1e-e75e-4310-bfa1-d5194c0ba98f

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact WilliamsonShmoys.exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hH