-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:25.123881+00:00
-- url     : https://prove2.me/submissions/fe7c71ea-1496-49af-a186-2b3f2cc7d34f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      3 * Fintype.card V - 6 = W.edgeSet.ncard := by
  obtain ⟨K, hUK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
      U hU
  have hKcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
      K hV hKdraw hKmax
  exact ⟨K, hUK, hKdraw, hKcount⟩