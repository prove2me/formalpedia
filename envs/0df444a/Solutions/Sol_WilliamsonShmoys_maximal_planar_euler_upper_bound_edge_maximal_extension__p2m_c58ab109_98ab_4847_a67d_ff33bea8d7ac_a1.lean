-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:53.915133+00:00
-- url     : https://prove2.me/submissions/635081a3-b9d6-4934-845d-0eee5130e664

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) := by
  exact WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK