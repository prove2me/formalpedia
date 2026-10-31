-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_add_one_edge__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:13.738985+00:00
-- url     : https://prove2.me/submissions/5d7fa6df-d4a4-4ebe-a834-1ebf9b748a34

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M.edgeSet ⊆ N.edgeSet)
    (hDrawM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hDrawN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : M.edgeSet.ncard < N.edgeSet.ncard) :
    ∃ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  obtain ⟨K, hMK, hKN, hKcard⟩ :=
    WilliamsonShmoys.planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
      M N hMN hcard
  exact ⟨K, hMK,
    WilliamsonShmoys.planar_drawing_subgraph__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
      N K hKN hDrawN,
    hKcard⟩