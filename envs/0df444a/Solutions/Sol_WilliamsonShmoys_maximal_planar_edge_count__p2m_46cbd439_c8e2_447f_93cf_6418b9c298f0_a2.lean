-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:57:51.131175+00:00
-- url     : https://prove2.me/submissions/85f9994c-c651-4870-bc3f-18ec61581a0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) : N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1 N hN hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1 N hN hCard hmax
  omega
