-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:25.972812+00:00
-- url     : https://prove2.me/submissions/9254b4be-c9fc-4ea0-8ac6-5c1cc9833d9d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1 K hcard hK
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1 K hcard hK hmax
  omega
