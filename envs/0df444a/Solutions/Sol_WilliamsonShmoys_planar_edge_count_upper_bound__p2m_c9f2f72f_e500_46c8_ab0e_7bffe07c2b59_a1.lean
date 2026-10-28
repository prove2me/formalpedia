-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:50:36.612032+00:00
-- url     : https://prove2.me/submissions/9b262500-ca26-424c-b15c-1879d4ee66ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hRH, _hHplanar, hHcard⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2
      R hR hCard
  have hEdges : R.edgeSet ⊆ H.edgeSet :=
    (SimpleGraph.edgeSetEmbedding V).monotone hRH
  have hCount : R.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hEdges
  omega