-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:44:45.235722+00:00
-- url     : https://prove2.me/submissions/636bc76d-2035-4eea-a19d-377cd74d7f25

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
    N hN hCard hmax
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
    N hN hCard
  omega