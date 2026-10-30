-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawing_edge_count__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:35.770598+00:00
-- url     : https://prove2.me/submissions/bd09c96b-b606-4f46-8e96-719597d1ac67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarSimpleGraphEdgeCount_upperBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2
import Theorems.Thm_WilliamsonShmoys_planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : ∀ N : SimpleGraph V, LE.le M N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planarSimpleGraphEdgeCount_upperBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2 M hM hV
  have hNoExtension : ¬ (M.edgeSet.ncard + 6 < 3 * Fintype.card V) := by
    intro hlt
    obtain ⟨N, hMN, hN, hNe⟩ :=
      WilliamsonShmoys.planarGraphCanBeExtended_belowTriangulationBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2 M hM hV hlt
    exact hNe (hmax N hMN hN)
  omega