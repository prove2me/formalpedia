-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:44:15.90369+00:00
-- url     : https://prove2.me/submissions/ca33154b-97ed-41e2-b142-8eabcf26305a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
import Theorems.Thm_WilliamsonShmoys_finite_graph_inclusion_cardinality_equality__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J →
          WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
      K hK
  refine ⟨H, hKH, hH, ?_⟩
  intro J hHJ hJ
  exact WilliamsonShmoys.finite_graph_inclusion_cardinality_equality__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
    H J hHJ (hmax J (le_trans hKH hHJ) hJ)