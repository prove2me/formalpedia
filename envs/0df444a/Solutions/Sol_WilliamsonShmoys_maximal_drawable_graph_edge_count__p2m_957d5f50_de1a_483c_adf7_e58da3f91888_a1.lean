-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:29:26.996886+00:00
-- url     : https://prove2.me/submissions/3b973003-d13a-44ce-b533-547ff106986c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLPlanar, hEdges⟩ :=
    WilliamsonShmoys.drawable_graph_triangulated_extension__p2m_a75193d8_91cd_4f7d_9e03_b4a5195cbe40_a1
      K hK hCard
  have hLK : L ≤ K := hMax L hKL hLPlanar
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hEdges