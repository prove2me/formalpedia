-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:06.053841+00:00
-- url     : https://prove2.me/submissions/10c11b14-3e76-42cb-b8db-f6df5456b1dd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.drawable_graph_maximal_extension__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
      K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c603be23_9a74_4dd9_9858_66dd86a4b903_a1
    L hL hCard hMax