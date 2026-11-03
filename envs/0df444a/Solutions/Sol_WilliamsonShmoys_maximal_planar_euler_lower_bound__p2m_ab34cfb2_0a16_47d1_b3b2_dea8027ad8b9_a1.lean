-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:54:17.266077+00:00
-- url     : https://prove2.me/submissions/853b6f43-7b71-4cda-a37e-4e18280ff835

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V ≤ K.edgeFinset.card + 6 := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have h := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1 K hK hcard hmax
  omega
