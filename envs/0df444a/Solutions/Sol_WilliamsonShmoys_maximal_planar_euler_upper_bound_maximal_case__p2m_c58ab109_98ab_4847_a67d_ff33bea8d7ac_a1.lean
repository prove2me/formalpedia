-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:57.060444+00:00
-- url     : https://prove2.me/submissions/b548a1e2-afb0-4c23-af01-5373beed2179

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1
    H hH hcard
