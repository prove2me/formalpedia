-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:26.737565+00:00
-- url     : https://prove2.me/submissions/b3869c14-a1bf-4d00-b0ae-e135617e54a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨T, hMT, _hTDraw, hTCard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_supergraph__p2m_44dff1e2_5719_47a8_9ed7_630e7dfea2be_a1
      M hDraw hCard
  have hEdges : M.edgeSet ⊆ T.edgeSet := SimpleGraph.edgeSet_mono hMT
  have hCount : M.edgeSet.ncard ≤ T.edgeSet.ncard := Set.ncard_mono hEdges
  omega