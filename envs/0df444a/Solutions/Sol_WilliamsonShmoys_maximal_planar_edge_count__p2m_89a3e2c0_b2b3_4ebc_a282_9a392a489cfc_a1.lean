-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:54:00.760178+00:00
-- url     : https://prove2.me/submissions/c161f1b8-9e2d-451c-91f4-0bb2c51a3373

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
    K hV hK
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
    K hV hK hmax
  exact Nat.le_antisymm hLower hUpper