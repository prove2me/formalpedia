-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:08.872221+00:00
-- url     : https://prove2.me/submissions/d5ce2a3a-daeb-484a-b907-3378ac40eb87

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_upper_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hupper := WilliamsonShmoys_maximal_planar_euler_upper_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1 K hK hcard
  have hlower := WilliamsonShmoys_maximal_planar_euler_lower_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1 K hK hconn hmax hcard
  omega